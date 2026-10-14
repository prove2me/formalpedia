-- Prove2me | solution 1 for ActuarialValuation.alterationSurrenderValue_zero_deduction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:30.017719+00:00
-- url     : https://prove2.me/submissions/04579e4b-e8a7-454e-8d85-b86fe492ad57

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationSurrenderValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V : ℝ) : alterationSurrenderValue V 0 = V := by
  simp [alterationSurrenderValue]
