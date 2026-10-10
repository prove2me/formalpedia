-- Prove2me | solution 1 for ActuarialValuation.cm1UnitFundStep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:14.820674+00:00
-- url     : https://prove2.me/submissions/84933a8e-41b9-4807-81e5-3fdb9ba154f7

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1UnitFundStep

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (U P C j : ℝ) (h : 0 ≤ U+P-C) (hj : -1 ≤ j) : 0 ≤ cm1UnitFundStep U P C j := by
  unfold cm1UnitFundStep
  exact mul_nonneg h (by linarith)
