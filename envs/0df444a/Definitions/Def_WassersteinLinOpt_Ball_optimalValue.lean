-- Prove2me | Definitions.Def_WassersteinLinOpt_Ball_optimalValue
-- name    : WassersteinLinOpt_Ball_optimalValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:44:37.807988+00:00
-- url     : https://prove2.me/theorems/4e0ed460-92ce-4790-9bff-f983a00a3b70
-- title:
--   Optimal value of problem (3)
-- statement:
--   Let $(X,d)$ be a metric space, $p\ge1$, $r>0$, $\nu\in\mathcal P(X)$ and $f:X\to\mathbb R$. Problem (3) is
--
--   $$\text{maximize}_{\mu}\ \int_X f(x)\,d\mu(x)\quad\text{subject to}\quad\mu\in\mathcal B_r(\nu),$$
--
--   and its **optimal value** is $\sup\{\int_X f\,d\mu:\mu\in\mathcal B_r(\nu)\}\in[-\infty,+\infty]$, with $\int_X f\,d\mu=\int[f]_+d\mu-\int[-f]_+d\mu$ the extended-real integral.
--
--   **Formalization Note.** `optimalValue p r ν f` is the supremum in `EReal` of `quasiIntegral f μ` over `μ ∈ wassersteinBall p r ν`. The value is "finite" when it is neither `⊤` nor `⊥`, and it is "attained" when some `μ` in the ball has `quasiIntegral f μ` equal to it.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1108, problem (3)

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- The optimal value of problem (3), p. 1108:
`sup { ∫_X f(x) dμ(x) : μ ∈ 𝓑_r(ν) }`, a supremum in `[−∞, +∞]` of the extended-real
integral `quasiIntegral`. -/
noncomputable def optimalValue {X : Type*} [MetricSpace X] [MeasurableSpace X] (p r : ℝ)
    (ν : ProbabilityMeasure X) (f : X → ℝ) : EReal :=
  ⨆ μ ∈ wassersteinBall p r ν, quasiIntegral f (μ : Measure X)

end WassersteinLinOpt.Ball


