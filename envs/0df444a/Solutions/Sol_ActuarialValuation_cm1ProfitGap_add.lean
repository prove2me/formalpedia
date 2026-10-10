-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitGap_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:58.2154+00:00
-- url     : https://prove2.me/submissions/a4a5e6c9-ccaf-4f51-8040-a8e6192b7e74

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b l m : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1ProfitGap (fun k => a k+b k) (fun k => l k+m k) n i = cm1ProfitGap a l n i + cm1ProfitGap b m n i := by
  unfold cm1ProfitGap cm1CashflowPV
  simp only [add_mul, Finset.sum_add_distrib]
  ring
