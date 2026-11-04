-- Prove2me | Definitions.Def_ChurnServiceMode_candidateValue
-- name    : ChurnServiceMode_candidateValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:42.314734+00:00
-- url     : https://prove2.me/theorems/98b3205e-8aa3-4a4d-b97e-031448a9b6d5
-- title:
--   The candidate value function $W(x,C_1,\dots,C_5)$ of Proposition 3
-- statement:
--   Proposition 3 builds the value function from four pieces:
--   $$V_1(x,C_1)=\frac{C_1}{x-\mu_S}+\mu_S,\qquad V_2(x,C_2,C_3)=C_2e^{\frac{(x-\mu_R)^2}{\sigma_R^2}}+C_3\operatorname{erf}\Bigl(\frac{x-\mu_R}{\sigma_R}\Bigr)e^{\frac{(x-\mu_R)^2}{\sigma_R^2}}+\mu_R,$$
--   $$V_3(x,C_4)=C_4+\mu_S\log(x-\mu_S),\qquad V_4(x,C_5)=C_5+\int_0^x\frac{\mu_R\sqrt\pi}{\sigma_R}e^{\frac{(z-\mu_R)^2}{\sigma_R^2}}\Bigl(1-\operatorname{erf}\Bigl(\frac{z-\mu_R}{\sigma_R}\Bigr)\Bigr)dz,$$
--   (displays (18)–(21)), glued along the thresholds:
--   $$W(x,C_1,\dots,C_5)=\begin{cases}V_1(x,C_1)&x\le\theta_G,\\ V_2(x,C_2,C_3)&\theta_G<x<q,\\ V_3(x,C_4)&q\le x\le\theta_b,\\ V_4(x,C_5)&x>\max\{q,\theta_b\}.\end{cases}$$
--
--   Each piece solves the ODE $B_i(x,V)=0$ of its region (Safe/Risky, unsatisfied/satisfied); Proposition 3 asserts that suitable constants make $W$ the value function.
--
--   **Formalization Note** The thresholds are extended reals and the four cases are tested in the printed order. Lean's convention $C_1/0=0$ makes $V_1(\mu_S)=\mu_S$; the point $x=\mu_S$ lies in the first region only when $\theta_G\ge\mu_S$, where continuous differentiability forces $C_1=0$. The logarithm is evaluated only at $x-\mu_S\ge q-\mu_S>0$ under Assumption 1. The integral in $V_4$ is oriented.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Proposition 3, displays (18)–(21), p.20

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- `V₁(x, C₁) = C₁/(x − μS) + μS`, display (18), p.20. -/
noncomputable def V1 (p : Params) (C₁ x : ℝ) : ℝ := C₁ / (x - p.μS) + p.μS

/-- `V₂(x, C₂, C₃) = C₂ e^{(x−μR)²/σR²} + C₃ erf((x−μR)/σR) e^{(x−μR)²/σR²} + μR`, display (19),
p.20. -/
noncomputable def V2 (p : Params) (C₂ C₃ x : ℝ) : ℝ :=
  C₂ * Real.exp ((x - p.μR) ^ 2 / p.σR ^ 2)
    + C₃ * erf ((x - p.μR) / p.σR) * Real.exp ((x - p.μR) ^ 2 / p.σR ^ 2) + p.μR

/-- `V₃(x, C₄) = C₄ + μS log(x − μS)`, display (20), p.20. -/
noncomputable def V3 (p : Params) (C₄ x : ℝ) : ℝ := C₄ + p.μS * Real.log (x - p.μS)

/-- `V₄(x, C₅) = C₅ + ∫₀ˣ (μR√π/σR) e^{(z−μR)²/σR²} (1 − erf((z−μR)/σR)) dz`, display (21), p.20
(oriented integral, so negative for `x < 0`). -/
noncomputable def V4 (p : Params) (C₅ x : ℝ) : ℝ :=
  C₅ + ∫ z in (0 : ℝ)..x, p.μR * Real.sqrt Real.pi / p.σR * Real.exp ((z - p.μR) ^ 2 / p.σR ^ 2)
    * (1 - erf ((z - p.μR) / p.σR))

/-- **The candidate value function `W(x, C₁, …, C₅)` of Proposition 3** (p.20):
`V₁(x, C₁)` if `x ≤ θG`; `V₂(x, C₂, C₃)` if `θG < x < q`; `V₃(x, C₄)` if `q ≤ x ≤ θb`;
`V₄(x, C₅)` if `x > max{q, θb}`.

**Formalization Note.** `θb, θG : EReal` and the comparisons are in `EReal`. The four cases are
tested in the printed order; for thresholds with `θG < q` (as Lemma 3 gives) they are disjoint and
exhaustive, and the last branch is exactly `x > max{q, θb}`. Lean's `C₁/0 = 0` makes `V₁(μS) = μS`;
this point lies in the first branch only when `θG ≥ μS`. `Real.log` is only evaluated at
`x − μS ≥ q − μS`, positive under Assumption 1. -/
noncomputable def W (p : Params) (θb θG : EReal) (C₁ C₂ C₃ C₄ C₅ : ℝ) (x : ℝ) : ℝ :=
  if (x : EReal) ≤ θG then V1 p C₁ x
  else if θG < (x : EReal) ∧ x < p.q then V2 p C₂ C₃ x
  else if p.q ≤ x ∧ (x : EReal) ≤ θb then V3 p C₄ x
  else V4 p C₅ x

end ChurnServiceMode


