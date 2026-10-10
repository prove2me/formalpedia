-- Prove2me | solution 1 for ActuarialValuation.cm1LoanBalance_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:43.879618+00:00
-- url     : https://prove2.me/submissions/ffdfe340-42f5-40be-890c-6cf46acf5d5c

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1LoanBalance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1LoanBalance c n 0 i = cm1CashflowPV c n i := by
  unfold cm1LoanBalance cm1CashflowPV
  apply Finset.sum_congr rfl
  intro k hk
  simp
