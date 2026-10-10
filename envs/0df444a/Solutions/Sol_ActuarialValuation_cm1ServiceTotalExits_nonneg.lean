-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceTotalExits_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:23.368118+00:00
-- url     : https://prove2.me/submissions/6a20b3ea-d1ed-4776-8187-78118176a69b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Definitions.Def_actuarial_cm1ServiceTotalExits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (N m : ℕ) (hd : ∀ t ∈ Finset.range N, 0 ≤ cm1ServiceAnnualExit d t m) : 0 ≤ cm1ServiceTotalExits d N m := by
  unfold cm1ServiceTotalExits
  exact Finset.sum_nonneg (fun t ht => hd t ht)
