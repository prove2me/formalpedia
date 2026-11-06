-- Prove2me | Definitions.Def_HOTrap_BatchAlg_run
-- name    : HOTrap_BatchAlg_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:47:56.626196+00:00
-- url     : https://prove2.me/theorems/ac624e36-d78f-48a5-bc87-07e945b74b89
-- title:
--   Output of a batched algorithm
-- statement:
--   The point returned by the algorithm with gradient oracle $g$ and seed $\omega$, namely the output map applied to all answers. For an objective $f$, the oracle is $g=\nabla f$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §2, pp.13–14

import Mathlib
import Definitions.Def_HOTrap_BatchAlg
import Definitions.Def_HOTrap_BatchAlg_answers

namespace HOTrap

/-- **The point returned** by the algorithm with gradient oracle `g` and seed `ω`. In use, `g = gradient f`.
Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, §2, pp.13–14. -/
noncomputable def BatchAlg.run {d : ℕ} {Ω : Type} (A : BatchAlg d Ω) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  A.output ω (A.answers g ω A.rounds)

end HOTrap


