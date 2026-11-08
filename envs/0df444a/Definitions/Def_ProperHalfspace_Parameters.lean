-- Prove2me | Definitions.Def_ProperHalfspace_Parameters
-- name    : ProperHalfspace_Parameters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:36.051707+00:00
-- url     : https://prove2.me/theorems/731909f4-c297-4451-a85a-eb0ce96295bb
-- title:
--   The structural error $\Delta_{\mathrm{str}}$ and the parameters (18)
-- statement:
--   The structural error is
--   $$\Delta_{\mathrm{str}}=C_0\Bigl(\nu+\frac{\sqrt{\alpha\log(1/\nu)\Lambda_\nu}}{\tau}+\sqrt{1-\rho}+\tau^{1/4}+\min\{1,\eta_E\}^{1/4}+\frac{\sqrt{\rho\lambda}}{1-\rho}\Bigr).$$
--   The parameter setting is $q_\varepsilon=\varepsilon/C_1$, $\rho=1-q_\varepsilon^2$, $\lambda=q_\varepsilon^6$, $\alpha=q_\varepsilon^{12}$, with $\tau=q_\varepsilon^4$ and $\nu=q_\varepsilon$, and $\eta_*=\sqrt{(1-\rho)\alpha/\lambda}$.
--
--   **Formalization Note** $\tau$ and $\nu$ of (18) do not occur in the statement of Corollary 20, so they have no Lean names here.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), (11), p.23; (18), p.26; Corollary 20, p.28

import Mathlib
import Definitions.Def_ProperHalfspace_Regularity

namespace ProperHalfspace

/-!
# The structural error `Δ_str` and the parameters of the proof of Theorem 1

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), (11), p.23; (18), p.26.
-/

/-- Equation (11), p.23:
`Δ_str = C₀ (ν + √(α log(1/ν) Λ_ν)/τ + √(1−ρ) + τ^{1/4} + min{1, η_E}^{1/4} + √(ρλ)/(1−ρ))`. -/
noncomputable def deltaStr (C₀ ρ α τ ν lamE ηE : ℝ) : ℝ :=
  C₀ * (ν + Real.sqrt (α * Real.log (1 / ν) * lam ν) / τ + Real.sqrt (1 - ρ) + τ ^ (1 / 4 : ℝ) +
    (min 1 ηE) ^ (1 / 4 : ℝ) + Real.sqrt (ρ * lamE) / (1 - ρ))

/-- `q_ε = ε / C₁`, (18), p.26. -/
noncomputable def qEps (C₁ ε : ℝ) : ℝ := ε / C₁

/-- `ρ = 1 − δ_sm = 1 − q_ε²`, (18), p.26. -/
noncomputable def rhoOf (C₁ ε : ℝ) : ℝ := 1 - qEps C₁ ε ^ 2

/-- `λ = q_ε⁶`, (18), p.26. -/
noncomputable def lambdaOf (C₁ ε : ℝ) : ℝ := qEps C₁ ε ^ 6

/-- `α = q_ε¹²`, (18), p.26. -/
noncomputable def alphaOf (C₁ ε : ℝ) : ℝ := qEps C₁ ε ^ 12

/-- `η_∗ = √((1−ρ)α/λ)`, Corollary 20, p.28. -/
noncomputable def etaStar (C₁ ε : ℝ) : ℝ :=
  Real.sqrt ((1 - rhoOf C₁ ε) * alphaOf C₁ ε / lambdaOf C₁ ε)

end ProperHalfspace


