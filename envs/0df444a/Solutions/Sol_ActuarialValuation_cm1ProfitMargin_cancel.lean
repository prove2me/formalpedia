-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitMargin_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:10.955793+00:00
-- url     : https://prove2.me/submissions/f2d419f3-9474-4711-a2e7-f84ff48cdc0e

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProfitMargin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (profitPV premiumPV : ℝ) (h : premiumPV ≠ 0) : cm1ProfitMargin profitPV premiumPV * premiumPV = profitPV := by
  unfold cm1ProfitMargin
  field_simp [h]
