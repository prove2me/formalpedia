-- Prove2me | solution 1 for ActuarialValuation.panjerUpperTail_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:18.849652+00:00
-- url     : https://prove2.me/submissions/f2a3ad85-cf10-499e-911d-c58f3cffa621

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerUpperTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (h : 0 ≤ g (n+1)) : panjerUpperTail g (n+1) ≤ panjerUpperTail g n := by
  unfold panjerUpperTail
  have hs : panjerAggregateCDF g n ≤ panjerAggregateCDF g (n + 1) := by
    change (∑ k ∈ Finset.range (n + 1), g k) ≤
      (∑ k ∈ Finset.range ((n + 1) + 1), g k)
    calc
      (∑ k ∈ Finset.range (n + 1), g k) ≤
          (∑ k ∈ Finset.range (n + 1), g k) + g (n + 1) :=
        le_add_of_nonneg_right h
      _ = (∑ k ∈ Finset.range ((n + 1) + 1), g k) :=
        (Finset.sum_range_succ g (n + 1)).symm
  linarith
