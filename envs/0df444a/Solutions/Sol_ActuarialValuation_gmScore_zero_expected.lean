-- Prove2me | solution 1 for ActuarialValuation.gmScore_zero_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:26:38.57536+00:00
-- url     : https://prove2.me/submissions/bb01f791-1a25-4782-8bc6-573ea7bb90c6

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claims exposure eta : ℝ)
    (h : claims = gmMean exposure eta) :
    gmScore claims exposure eta = 0 := by
  simp [gmScore, h]
