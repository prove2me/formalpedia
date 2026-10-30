-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
-- name    : StochasticProg_RecourseKKT_IsOptimalDEP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:27.129825+00:00
-- url     : https://prove2.me/theorems/e6546de6-30b7-4179-b03f-617985c57bf7
-- title:
--   Optimality in the deterministic equivalent program (1.2)
-- statement:
--   A point $x^*$ is **optimal in (1.2)** when $x^* \in K_1$ and
--
--   $$
--   c^{\mathsf T} x^* + \mathcal Q(x^*) \le c^{\mathsf T} x + \mathcal Q(x) \qquad \text{for every } x \in K_1,
--   $$
--
--   the comparison being made in the extended reals. This is "$x^*$ minimizes $c^{\mathsf T}x + \mathcal Q(x)$ over $K_1$" in the proof of Theorem 9.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.2), printed p. 104 (PDF p. 129), and Theorem 9 and its proof, printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_depObjective
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **Optimality in the deterministic equivalent program (1.2).**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.2), printed p. 104 (PDF p. 129), and Theorem 9, printed p. 116
(PDF p. 141): "A solution x* ∈ K₁, is optimal in (1.2)"; proof of Theorem 9: "x* minimizes
cᵀx + 𝒬(x) over K₁".

`xs` is optimal when it lies in `K₁` and its objective value `cᵀxs + 𝒬(xs)` is at most that of
every point of `K₁` (in the extended reals). -/
def IsOptimalDEP {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) (xs : Fin n1 → ℝ) : Prop :=
  xs ∈ firstStageSet pb.A pb.b ∧
    ∀ x ∈ firstStageSet pb.A pb.b, depObjective P pb xs ≤ depObjective P pb x

end StochasticProg.RecourseKKT


