-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoQ
-- name    : KallMayerSLP_RiskMeasures_rhoQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:13.079061+00:00
-- url     : https://prove2.me/theorems/5a594e5d-50c9-422b-8d97-be24f2a04620
-- title:
--   Quadratic deviation risk measure $\rho_Q$
-- statement:
--   For $\vartheta\in\mathcal L^2_1$, $\rho_Q(\vartheta):=\sqrt{\mathbb E[\vartheta^2]}$, the $L^2$ norm of $\vartheta$.
--
--   **Formalization Note** Used on $\mathcal L^2_1$, where $\vartheta^2$ is integrable.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §5.1, p.166 (PDF 176), and §7.2, Proposition 7.5 (F), p.187 (PDF 197)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Quadratic deviation risk measure `ρ_Q`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §5.1, p.166 (PDF 176), and §7.2, Prop. 7.5 (F), p.187 (PDF 197): `ρ_Q(ϑ) := √(𝔼[ϑ²])`, `ϑ ∈ 𝓛²₁`.

**Formalization Note.** Used on `𝓛²₁`, where `ϑ²` is integrable. -/
noncomputable def rhoQ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ ω, ϑ ω ^ 2 ∂P)

end KallMayerSLP.RiskMeasures


