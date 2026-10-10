-- Prove2me | solution 1 for ActuarialValuation.cm1ForceRiskDiscount_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:54.39935+00:00
-- url     : https://prove2.me/submissions/95ee8afb-8866-40a3-bb5a-e96702b21562

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_cm1ForceRiskDiscount
import Definitions.Def_actuarial_cm1ForceSurvival
import Definitions.Def_actuarial_cm1ForceDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ t : ℝ) : cm1ForceRiskDiscount δ μ t = cm1ForceDiscount δ t * cm1ForceSurvival μ t := by
  change Real.exp (-(δ + μ) * t) = Real.exp (-δ * t) * Real.exp (-μ * t)
  rw [show -(δ + μ) * t = -δ * t + -μ * t by ring, Real.exp_add]
