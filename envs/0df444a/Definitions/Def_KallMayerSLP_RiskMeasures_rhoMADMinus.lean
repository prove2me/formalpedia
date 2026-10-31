-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoMADMinus
-- name    : KallMayerSLP_RiskMeasures_rhoMADMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:14.960508+00:00
-- url     : https://prove2.me/theorems/30c7ed87-1cbf-4bab-ad21-6448938669c9
-- title:
--   Lower mean absolute semideviation $\rho^-_{\mathrm{MAD}}$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho^-_{\mathrm{MAD}}(\vartheta):=\mathbb E\big[(\vartheta-\mathbb E[\vartheta])^-\big]$, with $t^-=\max\{0,-t\}$.
--
--   **Formalization Note** $\mathbb E$ is the Lebesgue (Bochner) integral with respect to $P$; it is used only on $\mathcal L^1$, where it is the usual expectation. The identity $\rho^-_{\mathrm{MAD}}=\tfrac12\rho_{\mathrm{MAD}}$ printed with the definition is part of Proposition 7.6.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.6 (L), p.188 (PDF 198)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Lower mean absolute semideviation `ρ⁻_MAD`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.6 (L), p.188 (PDF 198): `ρ⁻_MAD(ϑ) := 𝔼[(ϑ − 𝔼[ϑ])⁻]`, `ϑ ∈ 𝓛¹₁`, with `z⁻ = max{0, −z}`.

**Formalization Note.** `𝔼` is the Bochner integral `∫ · ∂P`; it is meaningful on `𝓛¹`, the domain on which the risk measure is used (on non-integrable functions Lean's integral is `0`, which never enters a statement of this mission). The identity `ρ⁻_MAD = ½ ρ_MAD` printed with the definition is part of Prop. 7.6, not of this definition. -/
noncomputable def rhoMADMinus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, max (-(ϑ ω - ∫ ω', ϑ ω' ∂P)) 0 ∂P

end KallMayerSLP.RiskMeasures


