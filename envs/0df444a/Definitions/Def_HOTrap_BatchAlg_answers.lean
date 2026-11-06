-- Prove2me | Definitions.Def_HOTrap_BatchAlg_answers
-- name    : HOTrap_BatchAlg_answers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:58.303685+00:00
-- url     : https://prove2.me/theorems/6e5c6af4-4f73-43e7-9217-941101542d3d
-- title:
--   Transcript of a batched algorithm
-- statement:
--   The list of oracle answers after $r$ rounds. Round $r$ appends the oracle's answers at the queries of that round, in order, and these queries are computed from the seed and from the earlier answers.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, pp.13–14

import Mathlib
import Definitions.Def_HOTrap_BatchAlg

namespace HOTrap

/-- **The transcript of answers** after `r` rounds, when the oracle is `g` and the seed is `ω`: round `r`
appends `g` at each query point of the batch, in order. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, pp.13–14. -/
noncomputable def BatchAlg.answers {d : ℕ} {Ω : Type} (A : BatchAlg d Ω) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ω : Ω) :
    ℕ → List (EuclideanSpace ℝ (Fin d))
  | 0 => []
  | r + 1 => A.answers g ω r ++ List.ofFn (fun i => g (A.query r ω (A.answers g ω r) i))

end HOTrap


