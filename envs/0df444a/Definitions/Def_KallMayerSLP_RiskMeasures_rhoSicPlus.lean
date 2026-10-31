-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoSicPlus
-- name    : KallMayerSLP_RiskMeasures_rhoSicPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:08.60332+00:00
-- url     : https://prove2.me/theorems/361853ea-ff02-4f9a-9b5a-8f89e3ad62d5
-- title:
--   $\rho^+_{\mathrm{sic}}$: expected positive part
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho^+_{\mathrm{sic}}(\vartheta):=\mathbb E[\vartheta^+]$ with $t^+=\max\{0,t\}$: the expected shortfall of a separate integrated chance constraint (§4.1).
--
--   **Formalization Note** $\mathbb E$ is the Lebesgue (Bochner) integral with respect to $P$; it is used only on $\mathcal L^1$, where it is the usual expectation.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.4 (D1), p.186 (PDF 196)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **`ρ⁺_sic`, expected positive part.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.4 (D1), p.186 (PDF 196): `ρ⁺_sic(ϑ) := 𝔼[ϑ⁺]`, `ϑ ∈ 𝓛¹₁`, with `z⁺ = max{0, z}`.

**Formalization Note.** `𝔼` is the Bochner integral `∫ · ∂P`; it is meaningful on `𝓛¹`, the domain on which the risk measure is used (on non-integrable functions Lean's integral is `0`, which never enters a statement of this mission). -/
noncomputable def rhoSicPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, max (ϑ ω) 0 ∂P

end KallMayerSLP.RiskMeasures


