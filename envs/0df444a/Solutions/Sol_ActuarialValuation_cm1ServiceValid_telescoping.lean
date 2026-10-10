-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceValid_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:03.440264+00:00
-- url     : https://prove2.me/submissions/d6898830-d6bc-4515-97e0-6d23ece2a412

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
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

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m : ℕ) (h : cm1ServiceValid l d N m) : cm1ServiceTotalExits d N m + l N = l 0 := by
  have htelescope :
      ∀ n, cm1ServiceValid l d n m →
        cm1ServiceTotalExits d n m + l n = l 0 := by
    intro n
    induction n with
    | zero =>
        intro h
        simp [cm1ServiceTotalExits]
    | succ k ih =>
        intro h
        have hp : cm1ServiceValid l d k m := by
          intro t ht
          exact h t (Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self k)))
        have hs : l (k+1) + cm1ServiceAnnualExit d k m = l k :=
          h k (Finset.mem_range.mpr (Nat.lt_succ_self k))
        have hi := ih hp
        change (∑ t ∈ Finset.range k, cm1ServiceAnnualExit d t m) + l k = l 0 at hi
        change (∑ t ∈ Finset.range (k+1), cm1ServiceAnnualExit d t m) +
          l (k+1) = l 0
        rw [Finset.sum_range_succ]
        linarith
  exact htelescope N h
