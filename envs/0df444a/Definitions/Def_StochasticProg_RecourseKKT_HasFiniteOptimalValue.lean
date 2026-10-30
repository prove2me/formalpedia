-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_HasFiniteOptimalValue
-- name    : StochasticProg_RecourseKKT_HasFiniteOptimalValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:13.214423+00:00
-- url     : https://prove2.me/theorems/388a0dfd-8c0f-451b-942f-ea55934024b9
-- title:
--   Program (1.2) has a finite optimal value
-- statement:
--   Program (1.2) **has a finite optimal value** when
--
--   $$
--   -\infty < \inf_{x \in K_1} \big( c^{\mathsf T} x + \mathcal Q(x) \big) < +\infty ,
--   $$
--
--   the infimum being taken in the extended reals. It need not be attained. The value is $+\infty$ when no $x \in K_1$ has $\mathcal Q(x) < \infty$, in particular when $K_1$ is empty. This is the hypothesis of Theorem 9.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 9, printed p. 116 (PDF p. 141)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_depObjective
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **"(1.2) has a finite optimal value."**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, Theorem 9, printed p. 116 (PDF p. 141): "Suppose (1.2) has a finite optimal
value."

The infimum of `cᵀx + 𝒬(x)` over `x ∈ K₁`, taken in the extended reals, is neither `+∞` nor `−∞`.

**Formalization Note.** The optimal value is the `EReal` infimum (it need not be attained). It is
`+∞` when no point of `K₁` has `𝒬(x) < ∞`, in particular when `K₁ = ∅`. -/
def HasFiniteOptimalValue {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) : Prop :=
  (⨅ x ∈ firstStageSet pb.A pb.b, depObjective P pb x) ≠ ⊤ ∧
    (⨅ x ∈ firstStageSet pb.A pb.b, depObjective P pb x) ≠ ⊥

end StochasticProg.RecourseKKT


