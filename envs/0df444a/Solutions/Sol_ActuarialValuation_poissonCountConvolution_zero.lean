-- Prove2me | solution 1 for ActuarialValuation.poissonCountConvolution_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:26.851295+00:00
-- url     : https://prove2.me/submissions/52f13417-84ff-470a-bafd-bc0eaeb9fa05

import Mathlib
import Definitions.Def_actuarial_poissonCountConvolution
import Definitions.Def_actuarial_poissonCountMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) :
    poissonCountConvolution a b 0 =
      poissonCountMass a 0 * poissonCountMass b 0 := by
  simp [poissonCountConvolution]
