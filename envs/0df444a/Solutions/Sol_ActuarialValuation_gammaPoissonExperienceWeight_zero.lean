-- Prove2me | solution 1 for ActuarialValuation.gammaPoissonExperienceWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:41:25.844178+00:00
-- url     : https://prove2.me/submissions/20e4c3c4-22f5-433b-b671-3e523a0528e7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b : ℝ) :
  gammaPoissonExperienceWeight b 0 = 0 := by
  simp [gammaPoissonExperienceWeight]
