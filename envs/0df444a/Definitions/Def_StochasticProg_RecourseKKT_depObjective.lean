-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_depObjective
-- name    : StochasticProg_RecourseKKT_depObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:42.892031+00:00
-- url     : https://prove2.me/theorems/0bd497f5-42eb-4d26-9e04-b7caa58fe524
-- title:
--   Objective $c^{\mathsf T}x+\mathcal Q(x)$ of the deterministic equivalent program
-- statement:
--   The **deterministic equivalent program** (1.2) is
--
--   $$
--   \min\ z(x) = c^{\mathsf T} x + \mathcal Q(x) \quad \text{s.t. } A x = b,\ x \ge 0 .
--   $$
--
--   This definition is the objective $z(x) = c^{\mathsf T}x + \mathcal Q(x) \in [-\infty, +\infty]$, the sum of a real number and an extended real (so no $\infty - \infty$ case arises).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.2), printed p. 104 (PDF p. 129)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
open MeasureTheory Matrix

namespace StochasticProg.RecourseKKT

/-- **The objective `cᵀx + 𝒬(x)` of the deterministic equivalent program (1.2).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.2), printed p. 104 (PDF p. 129): "min z = cᵀx + 𝒬(x) s.t. Ax = b, x ≥ 0".

**Formalization Note.** A real number plus an `EReal`; no `⊥ + ⊤` case arises, so the value is
`+∞` exactly when `𝒬(x) = +∞` and `−∞` exactly when `𝒬(x) = −∞`. -/
noncomputable def depObjective {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) : EReal :=
  ((pb.c ⬝ᵥ x : ℝ) : EReal) + expectedRecourse P pb x

end StochasticProg.RecourseKKT


