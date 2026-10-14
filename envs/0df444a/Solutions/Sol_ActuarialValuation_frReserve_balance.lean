-- Prove2me | solution 1 for ActuarialValuation.frReserve_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T11:43:26.385114+00:00
-- url     : https://prove2.me/submissions/8b09fa76-4b92-43d8-a40d-ee89e3b8c549

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (assets premium benefit q s growth endDiscount : ℝ) (hs : frUddSurvival q s ≠ 0) : frFractionalReserve assets premium benefit q s growth endDiscount * frUddSurvival q s + s*q*benefit*endDiscount = (assets+premium)*growth := by
  unfold frFractionalReserve
  simp [hs]
