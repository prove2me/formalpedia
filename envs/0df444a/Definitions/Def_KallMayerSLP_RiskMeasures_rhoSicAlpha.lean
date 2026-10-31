-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoSicAlpha
-- name    : KallMayerSLP_RiskMeasures_rhoSicAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:04.261716+00:00
-- url     : https://prove2.me/theorems/5b099c27-4ff8-4b9f-96b0-16b8c9138e5a
-- title:
--   $\rho^\alpha_{\mathrm{sic}}$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$ and a parameter $\alpha$ (used with $0\le\alpha\le\tfrac12$),
--   $$
--   \rho^\alpha_{\mathrm{sic}}(\vartheta):=\alpha\,\mathbb E[\vartheta]+(1-2\alpha)\,\mathbb E[\vartheta^+]=\alpha\,\rho_{\mathrm E}(\vartheta)+(1-2\alpha)\,\rho^+_{\mathrm{sic}}(\vartheta).
--   $$
--
--   **Formalization Note** Defined by the second expression; the range of $\alpha$ is a hypothesis of the theorems that use it.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.4 (E), p.186 (PDF 196)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoE
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoSicPlus

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **`ρ^α_sic`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.4 (E), p.186 (PDF 196): `ρ^α_sic(ϑ) := α 𝔼[ϑ] + (1 − 2α) 𝔼[ϑ⁺] = α ρ_E(ϑ) + (1 − 2α) ρ⁺_sic(ϑ)`, `ϑ ∈ 𝓛¹₁`, `0 ≤ α ≤ 1/2`.

**Formalization Note.** Defined through the second expression; the parameter range `0 ≤ α ≤ 1/2` is a hypothesis of the theorems. -/
noncomputable def rhoSicAlpha {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℝ) (ϑ : Ω → ℝ) : ℝ :=
  α * rhoE P ϑ + (1 - 2 * α) * rhoSicPlus P ϑ

end KallMayerSLP.RiskMeasures


