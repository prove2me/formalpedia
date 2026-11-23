-- Prove2me | Definitions.Def_MarketInterference_FluidBias_Supplement_TwoLP
-- name    : MarketInterference_FluidBias_Supplement_TwoLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:43:54.344081+00:00
-- url     : https://prove2.me/theorems/00c39d85-77c5-4904-9e24-0373ed6c6caa
-- title:
--   Definition 4, pp. 16–17 — Poisson maximum-likelihood rates and the Two-LP estimator
-- statement:
--   Let $C_i,T_i,S_j$ be observed control, treatment and supply counts in a matching cycle of density $\tau>0$, and let $0<\rho<1$ be the treatment fraction. The Poisson maximum-likelihood estimates are
--   $$
--   \widehat\lambda_i=\frac{C_i}{(1-\rho)\tau},\qquad
--   \widehat\beta_i=\frac{T_i}{\rho\tau}-\widehat\lambda_i,\qquad
--   \widehat\pi_j=\frac{S_j}{\tau}.
--   $$
--   Using the published network value $\Phi=\Phi_1$, Definition 4 sets
--   $$
--   \widehat\Delta^\tau_{2LP}=\Phi(\widehat\lambda+\widehat\beta,\widehat\pi)-\Phi(\widehat\lambda,\widehat\pi).
--   $$
--   This is the plug-in definition, so its rescaled-count representation remains a theorem. `HasExperimentLaw` means a measurable count vector has precisely the published independent product-Poisson law: control means $(1-\rho)\lambda_i\tau$, treatment means $\rho(\lambda_i+\beta_i)\tau$, and supply means $\pi_j\tau$.
--
--   **Formalization Note** Demand and supply types use `Fin nd` and `Fin ns`; index $i$ represents the paper's $i+1$. The count order is ((control, treatment), supply). The existing general capacitated network and its value are imported without alteration. The clamp in the imported Poisson law is inactive under the theorem's nonnegative rates, positive density and open treatment fraction.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, pp. 16–17, Definition 4; p. 8, experiment

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Estimators
import Definitions.Def_MarketInterference_FiniteSample_Experiment

namespace MarketInterference.FluidBias.Supplement

open MeasureTheory

abbrev Counts (nd ns : ℕ) := ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ)

noncomputable def controlMLE {nd ns : ℕ} (ρ τ : ℝ) (z : Counts nd ns) : Fin nd → ℝ :=
  fun i => (z.1.1 i : ℝ) / ((1 - ρ) * τ)

noncomputable def treatmentMLE {nd ns : ℕ} (ρ τ : ℝ) (z : Counts nd ns) : Fin nd → ℝ :=
  fun i => (z.1.2 i : ℝ) / (ρ * τ)

noncomputable def effectMLE {nd ns : ℕ} (ρ τ : ℝ) (z : Counts nd ns) : Fin nd → ℝ :=
  treatmentMLE ρ τ z - controlMLE ρ τ z

noncomputable def supplyMLE {nd ns : ℕ} (τ : ℝ) (z : Counts nd ns) : Fin ns → ℝ :=
  fun j => (z.2 j : ℝ) / τ

/-- Definition 4: the plug-in estimator, before using Proposition 3's scaling identity. -/
noncomputable def twoLP {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (ρ τ : ℝ) (z : Counts nd ns) : ℝ :=
  Phi N 1 (controlMLE ρ τ z + effectMLE ρ τ z) (supplyMLE τ z) -
    Phi N 1 (controlMLE ρ τ z) (supplyMLE τ z)

/-- All coordinate independence is in the published product Poisson law. -/
def HasExperimentLaw {nd ns : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Counts nd ns) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ) : Prop :=
  Measurable X ∧ Measure.map X μ = MarketInterference.FiniteSample.experimentLaw lam beta pi ρ τ

end MarketInterference.FluidBias.Supplement


