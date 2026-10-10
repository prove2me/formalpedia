-- Prove2me | solution 1 for ActuarialValuation.cm1UDDFractionalSurvival_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:51.637307+00:00
-- url     : https://prove2.me/submissions/87128202-fed8-493d-8efc-a79996e49354

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1UDDFractionalSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℝ) : cm1UDDFractionalSurvival p 0 = 1 := by
  simp [cm1UDDFractionalSurvival]
