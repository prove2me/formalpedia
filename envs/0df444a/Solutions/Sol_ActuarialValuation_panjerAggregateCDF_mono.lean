-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateCDF_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:07:00.726119+00:00
-- url     : https://prove2.me/submissions/02fff8f8-7acc-4c72-b2f3-f3f7bcb5fa51

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (h : 0 ≤ g (n+1)) : panjerAggregateCDF g n ≤ panjerAggregateCDF g (n+1) := by
  change (∑ k ∈ Finset.range (n + 1), g k) ≤
    (∑ k ∈ Finset.range ((n + 1) + 1), g k)
  calc
    (∑ k ∈ Finset.range (n + 1), g k) ≤
        (∑ k ∈ Finset.range (n + 1), g k) + g (n + 1) :=
      le_add_of_nonneg_right h
    _ = (∑ k ∈ Finset.range ((n + 1) + 1), g k) :=
      (Finset.sum_range_succ g (n + 1)).symm
