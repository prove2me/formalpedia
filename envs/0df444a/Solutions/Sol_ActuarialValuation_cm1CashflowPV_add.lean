-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:52.727309+00:00
-- url     : https://prove2.me/submissions/fc43d4ee-2288-47d4-82a3-fd2e644f9dc3

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CashflowPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℕ → ℝ) (n : ℕ) (i : ℝ) : cm1CashflowPV (fun k => a k+b k) n i = cm1CashflowPV a n i + cm1CashflowPV b n i := by
  unfold cm1CashflowPV
  simp only [add_mul, Finset.sum_add_distrib]
