-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoE
-- name    : KallMayerSLP_RiskMeasures_rhoE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:04.154786+00:00
-- url     : https://prove2.me/theorems/a762a77e-aa9a-4ccb-a447-5f7faa311b6f
-- title:
--   Expectation risk measure $\rho_{\mathrm E}$
-- statement:
--   For a real random variable $\vartheta\in\mathcal L^1_1$ on $(\Omega,\mathcal F,P)$,
--   $$
--   \rho_{\mathrm E}(\vartheta):=\mathbb E[\vartheta].
--   $$
--
--   **Formalization Note** $\mathbb E$ is the Lebesgue (Bochner) integral with respect to $P$; it is used only on $\mathcal L^1$, where it is the usual expectation.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.3 (A), p.184 (PDF 194)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Expectation risk measure `ρ_E`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.3 (A), p.184 (PDF 194): `ρ_E(ϑ) := 𝔼[ϑ]`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** `𝔼` is the Bochner integral `∫ · ∂P`; it is meaningful on `𝓛¹`, the domain on which the risk measure is used (on non-integrable functions Lean's integral is `0`, which never enters a statement of this mission). -/
noncomputable def rhoE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, ϑ ω ∂P

end KallMayerSLP.RiskMeasures


