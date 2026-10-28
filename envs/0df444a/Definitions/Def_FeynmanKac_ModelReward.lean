-- Prove2me | Definitions.Def_FeynmanKac_ModelReward
-- name    : FeynmanKac_ModelReward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T21:49:57.91592+00:00
-- url     : https://prove2.me/theorems/5b0ffeca-ab90-4568-8637-b534c3d75048
-- title:
--   Discounted reward and Brownian integrand for a bounded diffusion
-- statement:
--   Specialise the published Feynman–Kac discounted-reward formula and the spatial-gradient Brownian integrand to the published bounded diffusion model. These definitions use actual state paths, coefficients and discount factors and assume no martingale or representation identity. Measurability and stochastic integrability are separate theorems.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_DiscountedReward
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory

namespace FeynmanKac.BoundedDiffusionModel

/-- The discounted classical-solution value together with accumulated
discounted running payments, instantiated on the actual diffusion path. -/
noncomputable def discountedReward {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  FeynmanKac.discountedReward
    m.path m.potential u m.runningSource m.initialTime s ω

/-- The predictable-integrand candidate for the space component of Itô's
formula. Its actual measurability and stochastic-integral admissibility
remain separate proof obligations. -/
noncomputable def discountedSpaceGradient
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  m.pathDiscount s ω *
    m.volatility (m.path s ω) s *
    deriv (fun x => u x s) (m.path s ω)

end FeynmanKac.BoundedDiffusionModel


