-- Prove2me | solution 1 for ActuarialValuation.dbCommutedPension_zero_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:29.725974+00:00
-- url     : https://prove2.me/submissions/4ed94ab5-3f84-4cc3-8b84-1b9e00660874

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutedPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f : ℝ) :
  dbCommutedPension g 0 f = g := by
  simp [dbCommutedPension]
