-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceMassPartition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:38.857984+00:00
-- url     : https://prove2.me/submissions/8a10ed70-8856-405d-83b6-76a23360dabe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceValid
import Definitions.Def_actuarial_cm1ServiceTotalExits
import Definitions.Def_actuarial_cm1ServiceTerminalMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (d : ℕ → ℕ → ℝ) (N m : ℕ) (h : cm1ServiceValid l d N m) (h0 : l 0 ≠ 0) : cm1ServiceTerminalMass l N + cm1ServiceTotalExits d N m / l 0 = 1 := by
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
  have hs := htelescope N h
  unfold cm1ServiceTerminalMass
  field_simp [h0]
  linarith
