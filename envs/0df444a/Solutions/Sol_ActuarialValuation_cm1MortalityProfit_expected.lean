-- Prove2me | solution 1 for ActuarialValuation.cm1MortalityProfit_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:15.864256+00:00
-- url     : https://prove2.me/submissions/61a5a30f-ec9b-4c40-80d7-c8594dd1f214

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1MortalityProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e a S : ℝ) (h : a=e) : cm1MortalityProfit e a S = 0 := by
  subst a
  simp [cm1MortalityProfit]
