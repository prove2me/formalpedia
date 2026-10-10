-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceAnnualExit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:42.192977+00:00
-- url     : https://prove2.me/submissions/0b20584c-ed7d-401c-8107-2072050ac1ef

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (t m : ℕ) (hd : ∀ j ∈ Finset.range m, 0 ≤ d t j) : 0 ≤ cm1ServiceAnnualExit d t m := by
  unfold cm1ServiceAnnualExit
  exact Finset.sum_nonneg (fun j hj => hd j hj)
