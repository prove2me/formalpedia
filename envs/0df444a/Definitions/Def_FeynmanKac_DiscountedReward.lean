-- Prove2me | Definitions.Def_FeynmanKac_DiscountedReward
-- name    : FeynmanKac_DiscountedReward
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T20:40:40.92528+00:00
-- url     : https://prove2.me/theorems/4b7b60e7-4140-481b-9b2f-6835647727ab
-- title:
--   Feynman–Kac discounted reward process
-- statement:
--   For an adapted diffusion, define the discounted classical-solution value plus accrued discounted running payments up to a time. The definition does not impose a martingale property, which must be proved from the PDE and stochastic calculus.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable def FeynmanKac.discountedReward {Ω : Type*}
    (X : ℝ → Ω → ℝ) (V u f : ℝ → ℝ → ℝ)
    (t s : ℝ) (ω : Ω) : ℝ :=
  FeynmanKac.pathDiscount X V t s ω * u (X s ω) s +
    ∫ r in t..s, FeynmanKac.pathDiscount X V t r ω * f (X r ω) r


