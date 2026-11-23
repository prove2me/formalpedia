-- Prove2me | Definitions.Def_MarketInterference_FluidBias_Supplement_UniformDesign
-- name    : MarketInterference_FluidBias_Supplement_UniformDesign
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:45:15.629235+00:00
-- url     : https://prove2.me/theorems/f07bc182-bb55-4a16-89ab-3bd7efac9cf9
-- title:
--   Theorem 8, pp. 26, 55 — uniform fraction and its conditional Poisson experiment
-- statement:
--   Let $U$ be the uniform probability measure on $[0,1]$, represented by Lebesgue measure restricted to that unit interval. The joint experiment first draws $\rho$ from $U$ and then, conditional on $\rho$, draws the independent control, treatment and supply Poisson counts with their source means. Thus its law is
--   $$
--   Q_\tau(d\rho,dz)=U(d\rho)\,P_{\rho,\tau}(dz),
--   $$
--   where $z=((C,T),S)$ and $P_{\rho,\tau}$ is the published experiment law. The mixed estimator is the published backward-difference SP estimator at this sampled fraction and count vector. It is assigned zero at the two null endpoints.
--
--   This construction preserves dependence of the arrivals on the sampled fraction. It is not the product of a uniform fraction and a fixed arrival distribution. Theorem 8 establishes both normalization of the resulting joint measure and integrability of its estimator.
--
--   **Formalization Note** The joint law is `Measure.bind` followed by the measurable map $z\mapsto(\rho,z)$. The map into measures is measurable: on the countable count space each atom probability is a finite product of continuous Poisson mass functions in the clamped means. Demand and supply indices are zero-based `Fin` indices. For $\rho\in[0,1]$ all source means are nonnegative, so no clamp changes them. Endpoint values change no expectation.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 8, experiment; pp. 26, 55, Theorem 8

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_TwoLP

namespace MarketInterference.FluidBias.Supplement

open MeasureTheory

/-- Lebesgue measure on the unit interval, whose length is one. -/
noncomputable def uniformFraction : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- First draw ρ uniformly, then draw the counts from their ρ-dependent experiment law. -/
noncomputable def uniformExperimentLaw {nd ns : ℕ}
    (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ) : Measure (ℝ × Counts nd ns) :=
  uniformFraction.bind (fun ρ =>
    (MarketInterference.FiniteSample.experimentLaw lam beta pi ρ τ).map (fun z => (ρ, z)))

/-- The null endpoints are assigned zero; on the open interval this is Definition 5 with (18). -/
noncomputable def mixedSP {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (τ : ℝ) (z : ℝ × Counts nd ns) : ℝ :=
  if 0 < z.1 ∧ z.1 < 1 then
    MarketInterference.FiniteSample.SPest N z.1 τ z.2.1.1 z.2.1.2 z.2.2 else 0

end MarketInterference.FluidBias.Supplement


