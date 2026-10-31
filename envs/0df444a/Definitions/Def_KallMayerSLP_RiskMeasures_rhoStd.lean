-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoStd
-- name    : KallMayerSLP_RiskMeasures_rhoStd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:11.633996+00:00
-- url     : https://prove2.me/theorems/1872191c-6ade-41f3-b007-e6dc10571f39
-- title:
--   Standard deviation $\rho_{\mathrm{Std}}=\sigma$
-- statement:
--   For $\vartheta\in\mathcal L^2_1$, $\rho_{\mathrm{Std}}(\vartheta):=\sigma(\vartheta):=\sqrt{\mathbb E[(\vartheta-\mathbb E[\vartheta])^2]}$.
--
--   **Formalization Note** Used on $\mathcal L^2_1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §5.1, p.169 (PDF 179), and §7.2, Proposition 7.6 (I), p.188 (PDF 198)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Standard deviation `ρ_Std = σ`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §5.1, p.169 (PDF 179), and §7.2, Prop. 7.6 (I), p.188 (PDF 198): `ρ_Std(ϑ) := σ(ϑ) := √(𝔼[(ϑ − 𝔼[ϑ])²])`, `ϑ ∈ 𝓛²₁`.

**Formalization Note.** Used on `𝓛²₁`. -/
noncomputable def rhoStd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ ω, (ϑ ω - ∫ ω', ϑ ω' ∂P) ^ 2 ∂P)

end KallMayerSLP.RiskMeasures


