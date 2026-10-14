-- Prove2me | solution 1 for ActuarialValuation.frReserve_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T11:41:46.087984+00:00
-- url     : https://prove2.me/submissions/22aed7e8-5d8e-44fa-ab34-ded4e6def126

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (assets premium q s growth endDiscount : ℝ) (hs : frUddSurvival q s ≠ 0) : frFractionalReserve assets premium 0 q s growth endDiscount * frUddSurvival q s = (assets+premium)*growth := by
  unfold frFractionalReserve
  simp [hs]
