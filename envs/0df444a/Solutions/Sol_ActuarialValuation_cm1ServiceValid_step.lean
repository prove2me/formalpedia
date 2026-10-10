-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceValid_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:51.428759+00:00
-- url     : https://prove2.me/submissions/c16918a0-b563-48bf-acf3-4a9d21be1f95

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Definitions.Def_actuarial_cm1ServiceValid
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m t : ℕ) (h : cm1ServiceValid l d N m) (ht : t < N) : l (t+1) + cm1ServiceAnnualExit d t m = l t := by
  exact h t (Finset.mem_range.mpr ht)
