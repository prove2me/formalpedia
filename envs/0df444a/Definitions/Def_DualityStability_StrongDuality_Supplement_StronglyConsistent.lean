-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_StronglyConsistent
-- name    : DualityStability_StrongDuality_Supplement_StronglyConsistent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:40:17.004342+00:00
-- url     : https://prove2.me/theorems/dcc1af07-649b-4d06-9634-b4ae2f9121b0
-- title:
--   Strong consistency (4.8), p. 177
-- statement:
--   In the standing setting of §3, the problem (P) is **strongly consistent** if there exists some $x\in E$ with
--
--   $$
--   x\in\operatorname{ri}C\quad\text{and}\quad Ax\in\operatorname{ri}D,
--   $$
--
--   where $\operatorname{ri}$ denotes the relative interior of a convex set: its interior with respect to the smallest affine manifold containing it. One and the same $x$ is required for both memberships.
--
--   Strong consistency is the finite-dimensional constraint qualification of Theorem 2.
--
--   **Formalization Note** The relative interior is Mathlib's `intrinsicInterior ℝ`, the interior of the set within its affine span. The paper uses "ri" only for finite-dimensional convex sets, and Theorem 2 is the only statement using it.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 177, (4.8)

import Definitions.Def_DualityStability_StrongDuality_Supplement_EffectiveDomains

namespace DualityStability.StrongDuality.Supplement

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- (P) is strongly consistent, (4.8), p. 177: some `x ∈ E` has `x ∈ ri C` and `Ax ∈ ri D`,
where `ri` is the relative interior (interior within the affine span). -/
def StronglyConsistent (p : Program E E' F F') : Prop :=
  ∃ x : E, x ∈ intrinsicInterior ℝ (effDomF p) ∧ p.A x ∈ intrinsicInterior ℝ (effDomG p)

end DualityStability.StrongDuality.Supplement


