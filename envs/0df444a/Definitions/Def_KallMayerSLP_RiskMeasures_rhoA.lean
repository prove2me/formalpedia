-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoA
-- name    : KallMayerSLP_RiskMeasures_rhoA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:09.194662+00:00
-- url     : https://prove2.me/theorems/5452360f-fd07-4242-97c3-d7cffb348286
-- title:
--   Absolute deviation risk measure $\rho_A$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho_A(\vartheta):=\mathbb E[|\vartheta|]$.
--
--   **Formalization Note** $\mathbb E$ is the Lebesgue (Bochner) integral with respect to $P$; it is used only on $\mathcal L^1$, where it is the usual expectation.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §5.2, (5.14), p.169 (PDF 179), and §7.2, Proposition 7.5 (G), p.187 (PDF 197)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Absolute deviation risk measure `ρ_A`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §5.2, (5.14), p.169 (PDF 179), and §7.2, Prop. 7.5 (G), p.187 (PDF 197): `ρ_A(ϑ) := 𝔼[|ϑ|]`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** `𝔼` is the Bochner integral `∫ · ∂P`; it is meaningful on `𝓛¹`, the domain on which the risk measure is used (on non-integrable functions Lean's integral is `0`, which never enters a statement of this mission). -/
noncomputable def rhoA {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, |ϑ ω| ∂P

end KallMayerSLP.RiskMeasures


