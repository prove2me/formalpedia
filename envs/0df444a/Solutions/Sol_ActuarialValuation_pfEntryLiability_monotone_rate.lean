-- Prove2me | solution 1 for ActuarialValuation.pfEntryLiability_monotone_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:05.554146+00:00
-- url     : https://prove2.me/submissions/e0ffcab6-3903-4509-83db-9be54d9c286d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryLiability
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pv payroll rate1 rate2 : ℝ) (hp : 0≤payroll) (h : rate1≤rate2) : pfEntryLiability pv payroll rate2≤pfEntryLiability pv payroll rate1 := by
  unfold pfEntryLiability
  have hm : rate1 * payroll ≤ rate2 * payroll :=
    mul_le_mul_of_nonneg_right h hp
  linarith
