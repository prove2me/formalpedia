-- Prove2me | Definitions.Def_BIInsurance_Screening_Logistic
-- name    : BIInsurance_Screening_Logistic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:02.563998+00:00
-- url     : https://prove2.me/theorems/a752ffb1-e738-49ea-870b-689970dcf0bb
-- title:
--   Eq. (3.3), p. 7 — the logistic density and the expected sales E[min(D, x)] of a capacity x under logistic demand
-- statement:
--   Let $\gamma>0$ and $m\in\mathbb R$. The **logistic density** with location $m$ and scale $\gamma$ is
--
--   $$
--   f_{m,\gamma}(x)=\frac{\exp\!\big(-(x-m)/\gamma\big)}{\gamma\,\big[1+\exp\!\big(-(x-m)/\gamma\big)\big]^{2}},\qquad x\in\mathbb R ,
--   $$
--
--   the density of a logistic random variable with mean $m$ and variance $\pi^2\gamma^2/3$. For a demand $D$ with this density and a capacity $x\in\mathbb R$, the **expected sales** are
--
--   $$
--   S_{m,\gamma}(x)=E[\min(D,x)]=\int_{-\infty}^{\infty}\min(t,x)\,f_{m,\gamma}(t)\,dt .
--   $$
--
--   In the business-interruption model of Kao, Keskin and Shang the per-period demand is $D_{ijt}=\mu_i+\delta_j+\epsilon_t$ with a logistic shock $\epsilon_t$ of mean $0$ and scale $\gamma$, so $D_{ijt}$ has density $f_{\mu_i+\delta_j,\gamma}$ (eq. (3.3)), and every revenue term of the model is $p$ times an expected-sales value $S_{\mu_i+\delta_j,\gamma}(\cdot)$.
--
--   **Formalization Note** `expSales γ m x` is the Bochner integral of `t ↦ min t x * logisticPDF γ m t` over $\mathbb R$ (Lebesgue measure). A Bochner integral is $0$ when the integrand is not integrable; the milestone for eq. (4.1) states integrability and the closed form, so no junk value can enter the model unnoticed.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 7, eq. (3.3); p. 11, eq. (4.1)

import Mathlib

namespace BIInsurance.Screening

/-- The logistic density (3.3) with location `m` and scale `γ`:
`f(x) = exp(-(x - m)/γ) / (γ (1 + exp(-(x - m)/γ))²)`. -/
noncomputable def logisticPDF (γ m x : ℝ) : ℝ :=
  Real.exp (-(x - m) / γ) / (γ * (1 + Real.exp (-(x - m) / γ)) ^ 2)

/-- Expected sales `E[min(D, x)]` of a capacity `x` when the demand `D` is logistic with
location `m` and scale `γ`, defined as the Lebesgue (Bochner) integral of `min t x` against
the logistic density. -/
noncomputable def expSales (γ m x : ℝ) : ℝ :=
  ∫ t, min t x * logisticPDF γ m t

end BIInsurance.Screening


