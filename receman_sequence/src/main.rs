use num_traits::{Zero};
use num_traits::One;

use stwo::{
    core::{
        channel::{ Blake2sChannel, Channel}, 
        fields::{qm31::{QM31, SecureField}, FieldExpOps}, 
        pcs::{CommitmentSchemeVerifier, PcsConfig}, 
        poly::circle::CanonicCoset, vcs::blake2_merkle::Blake2sMerkleChannel, verifier::verify, ColumnVec}, 
    prover::{
        backend::{
            simd::{column::BaseColumn, SimdBackend,  qm31::PackedSecureField, m31::{PackedM31, LOG_N_LANES},},
            Column
        }, 
        poly::{
            circle::{CircleEvaluation, PolyOps}, 
            BitReversedOrder}, 
    },
};
use stwo::prover::{prove, CommitmentSchemeProver};
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator, LogupTraceGenerator,relation, Relation
};
use stwo::core::air::Component;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    RelationEntry,
};

const LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR: u32 = 1;
const NUM_COLS: u32 = 3;
// relation!(PublicInputElements, 2);
pub struct PublicDataClaim {
    public_input: Vec<Vec<PackedM31>>,
}

impl PublicDataClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        for input in self.public_input.iter().flatten() {
            for v in input.to_array().iter() {
                channel.mix_u64(v.0 as u64);
            }
        }
    }
}

pub fn gen_trace(
    log_size: u32,
) -> (ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>, PublicDataClaim) {
    let mut cols: Vec<BaseColumn> = (0..NUM_COLS).map(|_| BaseColumn::zeros(1<<log_size)).collect();

    for simd_row in 0..(1<<log_size) {
        cols[0].set(simd_row, M31(0));
        cols[1].set(simd_row, M31((simd_row + 1) as u32));

       let mut holder = BaseColumn::zeros(NUM_COLS as usize);

        for c in 2..NUM_COLS {
           for (i, x) in cols.iter().enumerate() {
                let res = x.data.get(0).unwrap().to_array();
                let val = res.get(simd_row as usize).unwrap();
                holder.set(i, *val);
            }
            let prev_col = cols[(c-1) as usize].clone();
            let prev = prev_col.at(simd_row);
            let curr = prev.0.checked_sub(c);

            match curr {
                Some(curr) => {
                    let curr_exist = holder.as_slice().iter().find(|&&x| x == M31(curr)).is_some();
                    if curr != 0 && !curr_exist {
                        cols[c as usize].set(simd_row, M31(curr));

                    } else {
                        cols[c as usize].set(simd_row, prev + M31(c));
                    }
                },
                None => {
                    cols[c as usize].set(simd_row, prev + M31(c));
                }
            }
        }
    }

    let public_input: Vec<Vec<PackedM31>> = [cols[0].clone(), cols[1].clone()]
        .into_iter()
        .map(|col| col.data)
        .collect();

    // convert table to trace polynomial
    let domain = CanonicCoset::new(log_size as u32).circle_domain();
    let trace: ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> = 
            cols.clone()
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();
    (trace, PublicDataClaim{public_input})
}

struct IsFirstColumn {
    log_size: u32
}

impl IsFirstColumn {
    fn new(log_size: usize) -> Self {
        Self { log_size: log_size as u32 }
    }

    fn gen_column(&self) -> CircleEvaluation<SimdBackend, M31, BitReversedOrder> {
        let mut col = BaseColumn::zeros(1 << self.log_size);
        col.set(0, M31::from(1));
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        CircleEvaluation::new(domain, col)
    }

    fn id(&self) -> PreProcessedColumnId {
        PreProcessedColumnId { id: format!("is_first_{}", self.log_size) }
    }
}

struct RecamanEval {
    // is_first_column_id: PreProcessedColumnId,
    log_size: u32,
    lookup_elements: PublicInputElements,
}

impl FrameworkEval for RecamanEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        // let _is_first_column = eval.get_preprocessed_column(self.is_first_column_id.clone());

        let first = eval.next_trace_mask();
        let second = eval.next_trace_mask();

        // |a_{n}-a_{n-1}| = n (1 - 16)
        eval.add_constraint(second.clone() - first.clone() - second.clone());

        for i in 2..NUM_COLS {
            let mut previous = second.clone();
            let next = eval.next_trace_mask();

            // |a_{n}-a_{n-1}| = n
            eval.add_constraint((next.clone() - previous.clone() - E::F::from(M31::from(i))) * (next.clone() - previous.clone() + E::F::from(M31::from(i))));
            previous = next
        }

        // LogUp relation: -1/(c0 + alpha * c1 + alpha^2 * c9 - Z)
        eval.add_to_relation(RelationEntry::new(
            &self.lookup_elements,
            -E::EF::one(),
            &[first.clone(), second.clone()],
        ));
        eval.finalize_logup();

        eval
    }
}

// // 0 1 3 6
// // 0 2 4 1
// // 0 3 1 4
// // 0 4 2 5 
// // 0 5 3 6
// // 0 6 4 1
// // 0 7 5 2


relation!(PublicInputElements, 3);

fn main() {
    let num_rows: usize = 16;
    let log_num_rows: u32 = 4; // log2(16)

    let (trace, public_data_claim) = gen_trace(log_num_rows);

    println!("Config for FRI and PoW...");
    // Config for FRI and PoW
    let config = PcsConfig::default();

     println!("Precompute twiddles for evaluating and interpolating the trace...");
    // Precompute twiddles for evaluating and interpolating the trace
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_num_rows + LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR + config.fri_config.log_blowup_factor,)
        .circle_domain()
        .half_coset,
    );

     println!("Create the channel and commitment scheme...");
    // Create the channel and commitment scheme
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

     println!("Commit to the preprocessed trace...");
    // Create and commit to the preprocessed columns
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![]);
    tree_builder.commit(channel);
    println!("Commit to the preprocessed trace successful. ✅");
    
     // Commit to the size of the trace
    channel.mix_u64(log_num_rows as u64);

    // Commit to the public input
    public_data_claim.mix_into(channel);

    println!("Commit to the Interaction trace...");
    // Commit to the original trace columns
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);
    println!("Commit to the Interaction trace successful. ✅");

    // Draw random elements to use when creating the random linear combination of lookup values in the LogUp columns
    let lookup_elements = PublicInputElements::draw(channel);

    // Build logup column
    let mut log_up_gen = LogupTraceGenerator::new(log_num_rows);
    let mut col_gen = log_up_gen.new_col();
    for simd_row in 0..(1<<(log_num_rows - LOG_N_LANES)){
        let denom: PackedSecureField = lookup_elements.combine(&[trace[0].data[simd_row], trace[1].data[simd_row], ]);
        col_gen.write_frac(simd_row, -PackedSecureField::one(), denom);
    }
    col_gen.finalize_col();
    let (logup_cols, mut claimed_sum) = log_up_gen.finalize_last();

     //  commit to the LogUp columns
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(logup_cols);
    tree_builder.commit(channel);

     println!("Creating a component...");
    // Create a component
    let component = FrameworkComponent::<RecamanEval>::new(
        &mut TraceLocationAllocator::default(), 
        RecamanEval { 
            log_size: log_num_rows, 
            lookup_elements: lookup_elements.clone() 
        }, 
        claimed_sum);

    println!("Generating proof for execution trace...");
    // Prove
     let proof = prove(&[&component], channel, commitment_scheme).unwrap();
    println!("Proof generated successfully. ✅");

    println!("Verifying proof...");
    // Verify
    // Add the public values to the claimed sum
    let mut public_values = vec![PackedSecureField::zero(); 1 << (log_num_rows - LOG_N_LANES)];

    for simd_row in 0..(1 << (log_num_rows - LOG_N_LANES)) {
        let denom: PackedSecureField = lookup_elements.combine(&[
            trace[0].data[simd_row],
            trace[1].data[simd_row],
        ]);
        public_values[simd_row] = denom;
    }

    let public_values = PackedSecureField::batch_inverse(&public_values);

    for value in public_values.iter() {
        for v in value.to_array().iter() {
            claimed_sum += *v;
        }
    }

    assert_eq!(claimed_sum, SecureField::zero());

    let channel = &mut Blake2sChannel::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
    let sizes = component.trace_log_degree_bounds();

    commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
    channel.mix_u64((log_num_rows) as u64);
    public_data_claim.mix_into(channel);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);
    commitment_scheme.commit(proof.commitments[2], &sizes[2], channel);

    verify(&[&component], channel, commitment_scheme, proof).unwrap();
    println!("Proof verified successfully. ✅");

}
