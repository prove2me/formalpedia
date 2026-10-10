-- Prove2me | solution 1 for ActuarialValuation.cm1ForceRiskDiscount_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:28:00.568829+00:00
-- url     : https://prove2.me/submissions/18518630-261c-4a5e-94cd-aaf3813cde82

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceRiskDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ : ℝ) : cm1ForceRiskDiscount δ μ 0 = 1 := by
  simp [cm1ForceRiskDiscount]
