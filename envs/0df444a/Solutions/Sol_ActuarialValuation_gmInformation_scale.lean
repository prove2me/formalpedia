-- Prove2me | solution 1 for ActuarialValuation.gmInformation_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:39:21.785723+00:00
-- url     : https://prove2.me/submissions/c95e9c97-c9fb-42c2-aadf-e0c2940ada21

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmInformation
import Definitions.Def_actuarial_gmMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exposure multiplier eta : ℝ) :
    gmInformation (multiplier * exposure) eta =
      multiplier * gmInformation exposure eta := by
  simp only [gmInformation, gmMean, mul_assoc]
