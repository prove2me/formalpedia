-- Prove2me | Definitions.Def_FarmerInfoProvision_GaussianPrimitives
-- name    : FarmerInfoProvision_GaussianPrimitives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:23.956808+00:00
-- url     : https://prove2.me/theorems/1d260483-d61f-4ba2-bf23-854f7f5e897c
-- title:
--   Independent standard normal shocks on a probability space
-- statement:
--   The model is driven by independent normal shocks: $u\sim N(0,\sigma_u^2)$, $\epsilon_i\sim N(0,\sigma_f^2)$ for each farmer, and $\epsilon_r\sim N(0,\sigma_r^2)$, mutually uncorrelated and jointly normal, hence independent. A *Gaussian primitive* on a probability space $(\Omega,P)$ is a family $(Z_k)_{k\in\mathrm{Shock}(n)}$ of measurable, mutually independent random variables with $Z_k\sim N(0,1)$. The model's shocks are rescalings of these: $u=Z_{\mathrm{demand}}/\sqrt\alpha$, $\epsilon_r=Z_{\mathrm{public}}/\sqrt\beta$, and the private noises come from $Z_{\mathrm{private}\,i}$.
--
--   **Formalization Note** The probability space is a parameter: every result holds for every probability space carrying such a family. A concrete one (a product of standard Gaussians) exists, so the hypothesis is satisfiable.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, pp. 8–10

import Mathlib
import Definitions.Def_FarmerInfoProvision_Shock

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **A probability space carrying the model's independent standard normal shocks.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, pp. 8–9: `u ∼ N(0, σ_u²)`; `ϵ_i ∼ N(0, σ_f²)` with
"`Cov(u, ϵ_i) = 0`" and "`Cov(ϵ_i, ϵ_j) = 0`, `∀i ≠ j`"; `ϵ_r ∼ N(0, σ_r²)` "independent of `u`
and all `{ϵ_i}`'s" (p. 9); "`(u, x_1, ⋯, x_n, y)` are multi-variate normally distributed"
(p. 10).

`GaussianPrimitives P n` is a family `Z : Shock n → Ω → ℝ` of measurable random variables on
`(Ω, P)` that are mutually independent under `P`, each with law `N(0, 1)`. The model's shocks
are rescalings of these: `u = Z demand/√α`, `ϵ_r = Z publicNoise/√β`, and the private noises
come from `Z (privateNoise i)` (see `demandShock`, `publicSignal`, `privateObs`).

**Formalization Note.** The paper's noises are uncorrelated and jointly normal, hence
independent; independence is stated directly. The probability space is a parameter, not a
fixed product space: every result is stated for every probability space carrying such a
family. -/
structure GaussianPrimitives {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) where
  /-- The standard normal shocks. -/
  Z : Shock n → Ω → ℝ
  /-- Each shock is a random variable. -/
  measurable : ∀ k, Measurable (Z k)
  /-- The shocks are mutually independent. -/
  indep : iIndepFun Z P
  /-- Each shock is standard normal. -/
  law : ∀ k, P.map (Z k) = gaussianReal 0 1

end FarmerInfoProvision


