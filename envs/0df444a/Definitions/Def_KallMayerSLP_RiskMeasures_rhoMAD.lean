-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoMAD
-- name    : KallMayerSLP_RiskMeasures_rhoMAD
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:11.023695+00:00
-- url     : https://prove2.me/theorems/38dce763-0070-427e-b1c3-4e7c88f7326e
-- title:
--   Mean absolute deviation $\rho_{\mathrm{MAD}}$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho_{\mathrm{MAD}}(\vartheta):=\mathbb E\big[|\vartheta-\mathbb E[\vartheta]|\big]$.
--
--   **Formalization Note** $\mathbb E$ is the Lebesgue (Bochner) integral with respect to $P$; it is used only on $\mathcal L^1$, where it is the usual expectation.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.6 (J), p.188 (PDF 198)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Mean absolute deviation `ρ_MAD`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.6 (J), p.188 (PDF 198): `ρ_MAD(ϑ) := 𝔼[|ϑ − 𝔼[ϑ]|]`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** `𝔼` is the Bochner integral `∫ · ∂P`; it is meaningful on `𝓛¹`, the domain on which the risk measure is used (on non-integrable functions Lean's integral is `0`, which never enters a statement of this mission). -/
noncomputable def rhoMAD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, |ϑ ω - ∫ ω', ϑ ω' ∂P| ∂P

end KallMayerSLP.RiskMeasures


