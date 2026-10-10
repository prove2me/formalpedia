-- Prove2me | solution 1 for ActuarialValuation.cm1ForceDiscount_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:31:51.867165+00:00
-- url     : https://prove2.me/submissions/87d10582-56d3-41d5-b7d5-95879ebc55d5

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ s t : ℝ) : cm1ForceDiscount δ (s+t) = cm1ForceDiscount δ s * cm1ForceDiscount δ t := by
  change Real.exp (-δ * (s + t)) = Real.exp (-δ * s) * Real.exp (-δ * t)
  rw [mul_add, Real.exp_add]
