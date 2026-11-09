-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Batched
-- name    : BatchedFacilityLocation_Nonuniform_Batched
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:20.400712+00:00
-- url     : https://prove2.me/theorems/f71b1d8b-7fe3-4d5d-8255-fb5e8a933ccf
-- title:
--   Batched random-order algorithms on batch sequences and the two-copy algorithm
-- statement:
--   This file states the batched random-order model at the level of batch sequences, as needed for Observation 2.2 and Theorem 4.1.
--
--   **Algorithms.** An algorithm is represented by its expected cost $A(L)\in[0,\infty]$, over its internal randomness, when the batches arrive as the list $L$ (each batch the list of its clients' sites). For an instance, batch $b$ is revealed as the sites of its clients in index order; under batch order $\sigma$ the batch sequence is $(b_{\sigma^{-1}(1)},\dots,b_{\sigma^{-1}(B)})$, and the batched random-order expected cost is
--   $$\mathbb E[\mathrm{ALG}]=\frac1{B!}\sum_{\sigma}A(\text{batch sequence under }\sigma).$$
--   An ordinary random-order instance is one in which every client is its own batch.
--
--   **Combined algorithm.** Given $A_{RO}$ and $A_{BR}$, the combined algorithm runs $A_{RO}$ on the singleton batches and $A_{BR}$ on the batches of size at least two, each copy seeing its batches in their arrival order, with its own facilities and independent randomness; its cost is the sum of the two copies' costs, and a copy that receives no client costs $0$. The routing uses only the size of the arriving batch.
--
--   **The marginal Meyerson algorithm.** The single-copy algorithm shuffles each arriving batch uniformly at random and processes its clients one at a time by the rule of (4.2); its expected cost on $L$ averages over all $|l|!$ arrangements of each batch $l$ and integrates over the i.i.d. uniform lotteries. $\mathrm{ALG}_{\mathrm{comb}}$ is the combined algorithm with this algorithm in both copies.
--
--   **Formalization Note** Summing the copies' costs dominates the cost of the paper's version, which opens the union of the copies' facilities and connects each client to the closest one.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §2 p. 8 (Observation 2.2 and its proof), §3.1 p. 9 (two parallel copies), proof of Theorem 4.1 p. 24

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Algorithm

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

noncomputable section

open Classical

/-! # Batched random-order algorithms as functions of the batch sequence

§2, p. 7–8 (Observation 2.2), §3.1 p. 9 and proof of Theorem 4.1, p. 24 (the two-copy
algorithm). An algorithm is represented by its expected cost `A L ∈ [0,∞]` over its internal
randomness, given that the batches arrive as the list `L` (each batch a list of client sites).
Its batched random-order expected cost averages `A` over the uniform batch order. -/

variable {S : Type*} [Fintype S] [MetricSpace S]

/-- Batch `b` of instance `I` as revealed to the algorithm: the sites of its clients, listed in
client-index order (the adversary's presentation). -/
def batchList (I : Instance S) (b : Fin I.B) : List S :=
  ((List.finRange I.n).filter (fun i => decide (I.batch i = b))).map I.loc

/-- The batch sequence under batch order `σ` (`σ b` = arrival position of batch `b`). -/
def arrivalSeq (I : Instance S) (σ : Equiv.Perm (Fin I.B)) : List (List S) :=
  (List.finRange I.B).map (fun k => batchList I (σ.symm k))

/-- Expected cost of algorithm `A` on instance `I` in the batched random-order model:
the average of `A` over the `B!` equally likely batch orders. -/
def brExp (A : List (List S) → ℝ≥0∞) (I : Instance S) : ℝ≥0∞ :=
  ((I.B.factorial : ℝ≥0∞))⁻¹ * ∑ σ : Equiv.Perm (Fin I.B), A (arrivalSeq I σ)

/-- The ordinary random-order instance on clients `loc`: every client is its own batch. -/
def roInstance {n : ℕ} (loc : Fin n → S) : Instance S := ⟨n, n, loc, id⟩

/-- The singleton batches of a batch sequence, in their arrival order. -/
def singletonPart (L : List (List S)) : List (List S) :=
  L.filter (fun l => decide (l.length = 1))

/-- The nonsingleton batches of a batch sequence, in their arrival order. -/
def nonsingletonPart (L : List (List S)) : List (List S) :=
  L.filter (fun l => decide (2 ≤ l.length))

/-- The combined (two-copy) algorithm of Observation 2.2: `A_RO` is run on the singleton
batches and `A_BR` on the nonsingleton batches, each with its own facilities and independent
randomness, and its cost is the sum of the two copies' costs (a copy that receives no client
does nothing and costs `0`). The routing uses only the size of the arriving batch. -/
def combine (A_RO A_BR : List (List S) → ℝ≥0∞) (L : List (List S)) : ℝ≥0∞ :=
  (if singletonPart L = [] then 0 else A_RO (singletonPart L)) +
    (if nonsingletonPart L = [] then 0 else A_BR (nonsingletonPart L))

/-! ## The single-copy marginal Meyerson algorithm on a batch sequence -/

/-- Average of `g` over the independent uniform shuffles of the batches: each batch `l` is
replaced by each of its `|l|!` arrangements (`List.permutations`, counted by position), and the
shuffled batches are concatenated in arrival order. -/
def shuffleAvg : List (List S) → (List S → ℝ≥0∞) → ℝ≥0∞
  | [], g => g []
  | l :: Ls, g =>
      ((l.permutations.map (fun p => shuffleAvg Ls (fun r => g (p ++ r)))).sum) /
        (l.length.factorial : ℝ≥0∞)

/-- Expected cost of the marginal Meyerson algorithm processing the client sites `seq` one at a
time, in this order, from the empty open set, with i.i.d. uniform lotteries. -/
def seqCost (tb : TieBreak S) (f : S → ℝ) (seq : List S) : ℝ≥0∞ :=
  ∫⁻ U, ∑ k : Fin seq.length,
      (run tb f (fun k : Fin seq.length => seq.get k) U (List.finRange seq.length)).cost k
    ∂(lotteryLaw f (Fin seq.length))

/-- The single-copy batched algorithm (§4.1 with the in-batch shuffle of §2): each arriving
batch is shuffled uniformly at random and its clients are processed one at a time by the
marginal Meyerson rule. `mmAlg tb f L` is its expected cost given batch sequence `L`. -/
def mmAlg (tb : TieBreak S) (f : S → ℝ) (L : List (List S)) : ℝ≥0∞ :=
  shuffleAvg L (seqCost tb f)

/-- `ALG_comb`: the two-copy algorithm of §3.1 / Observation 2.2 / proof of Theorem 4.1 with the
marginal Meyerson algorithm in both copies. -/
def combAlg (tb : TieBreak S) (f : S → ℝ) (L : List (List S)) : ℝ≥0∞ :=
  combine (mmAlg tb f) (mmAlg tb f) L

end

end BatchedFacilityLocation.Nonuniform


