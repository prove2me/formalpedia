-- Prove2me | solution 1 for ActuarialValuation.gmRatingPremium_exposure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:47:44.823339+00:00
-- url     : https://prove2.me/submissions/2b8bb54a-4ebe-4ae9-ba70-adb3d13b76b9

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmRate
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmPurePremium
import Definitions.Def_actuarial_gmRatingPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exposure eta severity : ℝ) :
    gmRatingPremium exposure eta severity =
      exposure * gmPurePremium (gmRate eta) severity := by
  simp only [gmRatingPremium, gmPurePremium, gmRate, gmMean, mul_assoc]
