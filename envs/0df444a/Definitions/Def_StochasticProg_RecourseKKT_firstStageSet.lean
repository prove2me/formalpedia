-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
-- name    : StochasticProg_RecourseKKT_firstStageSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:28.289257+00:00
-- url     : https://prove2.me/theorems/37e8313c-6ac6-4503-af8c-205804b64a10
-- title:
--   First-stage feasible set $K_1$
-- statement:
--   The **first-stage feasible set** is the set of decisions satisfying the deterministic constraints:
--
--   $$
--   K_1 = \{\, x \in \mathbb R^{n_1} \mid A x = b,\ x \ge 0 \,\}.
--   $$
--
--   The inequality $x \ge 0$ is componentwise.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, printed p. 105 (PDF p. 130)

import Mathlib
open Matrix

namespace StochasticProg.RecourseKKT

/-- **The first-stage feasible set `K₁`.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1b, printed p. 105 (PDF p. 130): "Let K₁ = {x | Ax = b , x ≥ 0} be the set
determined by the fixed constraints".

**Formalization Note.** `0 ≤ x` is the componentwise order on `Fin n1 → ℝ`. -/
def firstStageSet {n1 m1 : ℕ} (A : Matrix (Fin m1) (Fin n1) ℝ) (b : Fin m1 → ℝ) :
    Set (Fin n1 → ℝ) :=
  {x | A *ᵥ x = b ∧ 0 ≤ x}

end StochasticProg.RecourseKKT


