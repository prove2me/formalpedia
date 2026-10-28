-- Prove2me | Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
-- name    : FeynmanKac_AdmissibleDiscountedGradient
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T08:32:02.866339+00:00
-- url     : https://prove2.me/theorems/4b73155a-ff02-468d-b025-8e35890eef85
-- title:
--   Genuine Brownian integrand and L² Itô integral for discounted spatial gradient
-- statement:
--   For clock-augmented diffusion X_s, Brownian time is elapsed τ=s−initialTime. Define space-gradient and discounted-gradient coefficients at Brownian τ using state X(initialTime+τ), extending by zero outside [0,T−initialTime]. Define independent admissibility with joint measurability, progressive measurability, and all-positive-horizon Brownian L² energy. Define two actual stochastic integrals by stochasticIntegralBrownian at elapsed time s−initialTime. This definition assumes no Itô formula, martingale identity or Feynman–Kac result.
-- source:
--   LevyStochCalc/Brownian/ItoL2CompletionMaster and clock-augmented FeynmanKac_BoundedDiffusionModel, pinned Prove2Me mathlib 0df444a

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open scoped NNReal ENNReal

namespace FeynmanKac.BoundedDiffusionModel

/-- Gradient coefficient at Brownian elapsed time r, zero beyond the horizon. -/
noncomputable def spaceGradientIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  if r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime) then
    m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) *
      deriv (fun x => u x (m.initialTime + r))
        (m.path (m.initialTime + r) ω)
  else 0

/-- The discounted gradient at elapsed time r of the driving Brownian motion. -/
noncomputable def discountedGradientIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  m.pathDiscount (m.initialTime + r) ω *
    m.spaceGradientIntegrand u ω r

/-- Integrability and adaptedness hypotheses for the non-discounted integral. -/
def AdmissibleSpaceGradient
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry (m.spaceGradientIntegrand u)) ∧
  LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration
    (m.spaceGradientIntegrand u) ∧
  ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖m.spaceGradientIntegrand u ω r‖₊ : ℝ≥0∞) ^ 2
        ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤

/-- Integrability and adaptedness hypotheses for the discounted integral. -/
def AdmissibleDiscountedGradient
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry (m.discountedGradientIntegrand u)) ∧
  LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration
    (m.discountedGradientIntegrand u) ∧
  ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖m.discountedGradientIntegrand u ω r‖₊ : ℝ≥0∞) ^ 2
        ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤

/-- Brownian integral from elapsed 0 to absolute s of the spatial gradient. -/
noncomputable def spaceGradientItoIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (h : m.AdmissibleSpaceGradient u)
    (s : ℝ) (ω : Ω) : ℝ :=
  LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
    (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (m.spaceGradientIntegrand u) h.1 h.2.1 h.2.2
    (s - m.initialTime) ω

/-- Brownian integral from elapsed 0 to absolute s of the discounted gradient. -/
noncomputable def discountedGradientItoIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (h : m.AdmissibleDiscountedGradient u)
    (s : ℝ) (ω : Ω) : ℝ :=
  LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
    (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (m.discountedGradientIntegrand u) h.1 h.2.1 h.2.2
    (s - m.initialTime) ω

end FeynmanKac.BoundedDiffusionModel


