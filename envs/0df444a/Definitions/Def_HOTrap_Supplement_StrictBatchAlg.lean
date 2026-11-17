-- Prove2me | Definitions.Def_HOTrap_Supplement_StrictBatchAlg
-- name    : HOTrap_Supplement_StrictBatchAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:28:23.523191+00:00
-- url     : https://prove2.me/theorems/75f4fe72-8789-490b-adf5-bb3038767ef3
-- title:
--   Strict value-only and gradient-only batched oracle algorithms
-- statement:
--   A **strict batched oracle algorithm** has a fixed number of adaptive rounds and a fixed batch size in each round. Each query point is computed only from the internal seed and responses from earlier rounds, and the terminal output is computed only from the seed and the complete response transcript.
--
--   The response type fixes the oracle. For a value-only algorithm it is $\mathbb R$, so a response is exactly $f(x)$. For a gradient-only algorithm it is $\mathbb R^d$, so a response is exactly $\nabla f(x)$. Thus neither algorithm can inspect the other oracle component or any higher derivative. The sum of the batch sizes is a deterministic worst-case query budget, uniform over objectives and seeds; unrestricted finite offline computation is not charged.
--
--   This definition supplies the strict oracle model used by Theorems 3.1, 5.1, and 5.2.
--
--   **Formalization Note** Deterministic algorithms use the one-point seed space. A shorter execution may pad its fixed budget with dummy queries.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, pp.13–14; §5, pp.27–28

import Mathlib

namespace HOTrap.Supplement

/-- A **strict batched oracle algorithm** whose only information about the objective is a response
of type `R` at each query.  Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order
Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Section 2,
pp.13--14, and Section 5, pp.27--28.

The response type distinguishes the paper's strict oracles: `R = ℝ` is value-only and
`R = EuclideanSpace ℝ (Fin d)` is gradient-only.  Queries in a round depend only on earlier
responses, and the output sees only the resulting response transcript.

**Formalization Note.** Batch sizes and the number of rounds are fixed before the objective is
seen, so `numQueries` is a worst-case budget for every objective.  A shorter execution may be
padded with dummy queries.  `Unit` is the deterministic seed space used by the supplement's upper
bounds.  Offline computation is unrestricted. -/
structure StrictBatchAlg (d : ℕ) (R : Type*) (Ω : Type*) where
  rounds : ℕ
  batch : ℕ → ℕ
  query : (r : ℕ) → Ω → List R → Fin (batch r) → EuclideanSpace ℝ (Fin d)
  output : Ω → List R → EuclideanSpace ℝ (Fin d)

/-- The response transcript after `r` rounds of a strict batched algorithm. -/
noncomputable def StrictBatchAlg.answers {d : ℕ} {R Ω : Type*}
    (A : StrictBatchAlg d R Ω) (oracle : EuclideanSpace ℝ (Fin d) → R) (ω : Ω) :
    ℕ → List R
  | 0 => []
  | r + 1 =>
      A.answers oracle ω r ++
        List.ofFn (fun i => oracle (A.query r ω (A.answers oracle ω r) i))

/-- The point returned after all rounds. -/
noncomputable def StrictBatchAlg.run {d : ℕ} {R Ω : Type*}
    (A : StrictBatchAlg d R Ω) (oracle : EuclideanSpace ℝ (Fin d) → R) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  A.output ω (A.answers oracle ω A.rounds)

/-- The fixed worst-case number of oracle queries. -/
def StrictBatchAlg.numQueries {d : ℕ} {R Ω : Type*} (A : StrictBatchAlg d R Ω) : ℕ :=
  ∑ r ∈ Finset.range A.rounds, A.batch r

end HOTrap.Supplement


