-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceValid_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:58.436193+00:00
-- url     : https://prove2.me/submissions/420eefee-d46a-4ab9-9a26-6dc79fb1f011

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

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m t : ℕ) (h : cm1ServiceValid l d N m) (ht : t < N) (hd : 0 ≤ cm1ServiceAnnualExit d t m) : l (t+1) ≤ l t := by
  have hs : l (t+1) + cm1ServiceAnnualExit d t m = l t :=
    h t (Finset.mem_range.mpr ht)
  linarith
