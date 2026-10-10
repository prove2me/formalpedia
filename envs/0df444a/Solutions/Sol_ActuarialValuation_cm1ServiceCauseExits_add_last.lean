-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceCauseExits_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:40.425028+00:00
-- url     : https://prove2.me/submissions/bd31cb42-d407-44ca-979e-ddb247a2f529

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceCauseExits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (N j : ℕ) : cm1ServiceCauseExits d (N+1) j = cm1ServiceCauseExits d N j + d N j := by
  simp [cm1ServiceCauseExits, Finset.sum_range_succ]
