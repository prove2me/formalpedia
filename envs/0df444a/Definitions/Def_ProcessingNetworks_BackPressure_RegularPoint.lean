-- Prove2me | Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint
-- name    : ProcessingNetworks_BackPressure_RegularPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:19:55.441637+00:00
-- url     : https://prove2.me/theorems/c9336dfa-0150-4cec-bbfd-0d7f2f7b998f
-- title:
--   Regular point (Definition 8.7), restated
-- statement:
--   Restated from mission V (Definition 8.7): a point $t>0$ is regular for a fluid model solution
--   if all four components are differentiable there. Used here for Theorem 9.8's "at each regular
--   point" qualifier.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 138, Definition 8.7 (restated)

import Mathlib

namespace ProcessingNetworks.BackPressure

/-- Definition 8.7 (regular point), restated from mission V's `RegularPoint` (drafts in this
series do not import one another): a point `t > 0` is regular for a fluid model solution
`(D,F,T,Z)` if all four components are differentiable at `t`. -/
def RegularPoint {I J : ℕ} (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (t : ℝ) : Prop :=
  DifferentiableAt ℝ Dh t ∧ DifferentiableAt ℝ Fh t ∧ DifferentiableAt ℝ Th t ∧
    DifferentiableAt ℝ Zh t

end ProcessingNetworks.BackPressure


