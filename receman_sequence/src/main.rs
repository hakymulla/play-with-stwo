use num_traits::{Zero};
use stwo::{
    core::{
        channel::{ Blake2sChannel, Channel}, 
        fields::{qm31::QM31,}, 
        pcs::{CommitmentSchemeVerifier, PcsConfig}, 
        poly::circle::CanonicCoset, vcs::blake2_merkle::Blake2sMerkleChannel, verifier::verify, ColumnVec}, 
    prover::{
        backend::{
            simd::{column::BaseColumn, m31::{LOG_N_LANES}, 
            SimdBackend},
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
    EvalAtRow, FrameworkComponent, FrameworkEval, TraceLocationAllocator
};
use stwo::core::air::Component;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

const LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR: u32 = 1;
const NUM_COLS: u32 = 10;

pub fn gen_trace(
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> {
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

    // convert table to trace polynomial
    let domain = CanonicCoset::new(log_size as u32).circle_domain();
    let trace: ColumnVec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>> = 
            cols
            .into_iter()
            .map(|col| CircleEvaluation::new(domain, col))
            .collect();
    trace
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
    is_first_column_id: PreProcessedColumnId,
    log_size: u32
}

impl FrameworkEval for RecamanEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let _is_first_column = eval.get_preprocessed_column(self.is_first_column_id.clone());

        let first = eval.next_trace_mask();
        let mut second = eval.next_trace_mask();
        // |a_{n}-a_{n-1}| = n (1 - 16)
        eval.add_constraint(second.clone() - first.clone() - second.clone());

        for i in 2..NUM_COLS {
            let next = eval.next_trace_mask();
            // |a_{n}-a_{n-1}| = n
            eval.add_constraint((next.clone() - second.clone() - E::F::from(M31::from(i))) * (next.clone() - second.clone() + E::F::from(M31::from(i))));
            second = next
        }
        eval
    }
}


fn main() {
    let log_size = LOG_N_LANES;

    // Config for FRI and PoW
    println!("Config for FRI and PoW...");
    let config = PcsConfig::default();

    // Precompute twiddles for evaluating and interpolating the trace
    println!("Precompute twiddles for evaluating and interpolating the trace...");
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(log_size + LOG_CONSTRAINT_EVAL_BLOWUP_FACTOR + config.fri_config.log_blowup_factor,)
        .circle_domain()
        .half_coset,
    );

     // Create the channel and commitment scheme
    println!("Create the channel and commitment scheme...");
    let channel = &mut Blake2sChannel::default();
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, Blake2sMerkleChannel>::new(config, &twiddles);

    // Commit to the preprocessed trace
    println!("Commit to the preprocessed trace...");
    let is_first_column = IsFirstColumn::new(log_size as usize);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![is_first_column.gen_column()]);
    tree_builder.commit(channel);
    println!("Commit to the preprocessed trace successful. ✅");
    
    // Commit to the size of the trace
    channel.mix_u64(log_size as u64);

   // Create and commit to the trace columns
    println!("Commit to the Interaction trace...");
    let trace = gen_trace(log_size);
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.clone());
    tree_builder.commit(channel);
    println!("Commit to the Interaction trace successful. ✅");

    // Create a component
    println!("Creating a component...");
    let component = FrameworkComponent::<RecamanEval>::new(
        &mut TraceLocationAllocator::default(),
        RecamanEval {
            is_first_column_id: is_first_column.id(),
            log_size,
        },
        QM31::zero(),
    );

    // Prove
    println!("Generating proof for execution trace...");
    let proof = prove(&[&component], channel, commitment_scheme).unwrap();
    println!("Proof generated successfully. ✅");

    // Verify
    println!("Verifying proof...");
    let channel = &mut Blake2sChannel::default();
    let commitment_scheme = &mut CommitmentSchemeVerifier::<Blake2sMerkleChannel>::new(config);
    let sizes = component.trace_log_degree_bounds();

    commitment_scheme.commit(proof.commitments[0], &sizes[0], channel);
    channel.mix_u64(log_size as u64);
    commitment_scheme.commit(proof.commitments[1], &sizes[1], channel);

    verify(&[&component], channel, commitment_scheme, proof).unwrap();
    println!("Proof verified successfully. ✅");
}

// 0 1 3 6
// 0 2 4 1
// 0 3 1 4
// 0 4 2 5 
// 0 5 3 6
// 0 6 4 1
// 0 7 5 2