-- Prove2me | Definitions.Def_ProcessingNetworks_LyapunovCriteria_RegularPoint
-- name    : ProcessingNetworks_LyapunovCriteria_RegularPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:55:23.881694+00:00
-- url     : https://prove2.me/theorems/5549e68a-32e0-4c9b-8152-79af0d3f0c6e
-- title:
--   Definition 8.7 — regular point of a fluid model solution
-- statement:
--   **Definition 8.7.** A point $t > 0$ is a **regular point** for a fluid model solution
--   $(D,F,T,Z)$ if all four components are differentiable at $t$.
--
--   Because every fluid model solution is (globally) Lipschitz (Lemma 8.3), hence absolutely
--   continuous, the set of non-regular points has Lebesgue measure zero — so restricting
--   attention to regular points loses nothing when verifying an almost-everywhere drift
--   condition.
--
--   **Formalization note.** Remark 8.8 observes that, because (6.4) defines $F$ from $T$, (6.3)
--   defines $D$ from $F$, and (6.1) defines $Z$ from $F$ and $D$, a point is regular iff $T$
--   alone is differentiable there; this mission still states differentiability of all four
--   components explicitly, matching Definition 8.7's own wording exactly rather than the
--   (equivalent, but definition-external) simplification of Remark 8.8.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 138, Definition 8.7

import Mathlib
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_FluidEquationData

namespace ProcessingNetworks.LyapunovCriteria

/-- Definition 8.7 (regular point), Dai & Harrison p. 138 (PDF p. 154): a point `t > 0` is a
regular point for a fluid model solution `(D, F, T, Z)` if all four of its components are
differentiable at `t`. -/
def RegularPoint {I J : ℕ} (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ)
    (t : ℝ) : Prop :=
  DifferentiableAt ℝ Dh t ∧ DifferentiableAt ℝ Fh t ∧ DifferentiableAt ℝ Th t ∧
    DifferentiableAt ℝ Zh t

end ProcessingNetworks.LyapunovCriteria


