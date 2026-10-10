-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:34.381086+00:00
-- url     : https://prove2.me/submissions/1aff2f02-8442-40d6-9253-ae702aa5c139

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1CashflowPV c (n+1) i = cm1CashflowPV c n i + c n * cm1Discount i (n+1) := by
  simp [cm1CashflowPV, Finset.sum_range_succ]
