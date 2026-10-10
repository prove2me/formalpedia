-- Prove2me | solution 1 for ActuarialValuation.cm1LifeDecrement_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:39.082249+00:00
-- url     : https://prove2.me/submissions/32ea7668-f5e9-4711-9440-76408f8d1377

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeDecrement
import Mathlib.Tactic.Ring
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) : (∑ k ∈ Finset.range n, cm1LifeDecrement l x k) = l x - l (x+n) := by
  induction n with
  | zero => simp [cm1LifeDecrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [cm1LifeDecrement]
      have ha : x + n + 1 = x + (n + 1) := by omega
      rw [ha]
      ring
