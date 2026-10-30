-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
-- name    : StochasticProg_RecourseKKT_secondStageFeasSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:08.374622+00:00
-- url     : https://prove2.me/theorems/706fb752-7510-4584-b061-c626e9be105f
-- title:
--   Second-stage feasibility set $K_2=\{x\mid\mathcal Q(x)<\infty\}$
-- statement:
--   The **second-stage feasibility set** is the effective domain of the expected recourse function:
--
--   $$
--   K_2 = \{\, x \in \mathbb R^{n_1} \mid \mathcal Q(x) < \infty \,\}.
--   $$
--
--   These are the first-stage decisions whose expected recourse cost is not $+\infty$; for a finite distribution it is the intersection of the sets $K_2(\xi)$ over the realizations of positive probability. It is the set $K_2$ of Theorems 6 and 9.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, printed p. 109 (PDF p. 134)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **The second-stage feasibility set `K₂ = {x | 𝒬(x) < ∞}`.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, printed p. 109 (PDF p. 134): "When ξ is not a discrete random variable, we
may now define K₂ in two different ways: K₂ = {x | 𝒬(x) < ∞}". This is the definition of `K₂` used
by Theorems 6 and 9.

**Formalization Note.** `𝒬` is `expectedRecourse`, valued in `EReal`, so `< ⊤` is "`< ∞`". -/
def secondStageFeasSet {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) : Set (Fin n1 → ℝ) :=
  {x | expectedRecourse P pb x < ⊤}

end StochasticProg.RecourseKKT


