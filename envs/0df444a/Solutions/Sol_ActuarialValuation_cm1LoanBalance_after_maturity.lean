-- Prove2me | solution 1 for ActuarialValuation.cm1LoanBalance_after_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:46.939028+00:00
-- url     : https://prove2.me/submissions/badb3136-9046-4089-bb61-3820c56e03dc

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1LoanBalance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n t : ℕ) (i : ℝ) (h : n ≤ t) : cm1LoanBalance c n t i = 0 := by
  unfold cm1LoanBalance
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hnot : ¬ t < k + 1 := by omega
  simp [hnot]
