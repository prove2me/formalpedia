-- Prove2me | solution 1 for ActuarialValuation.panjerStopLoss_mono_truncation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:20:06.695974+00:00
-- url     : https://prove2.me/submissions/a4650c53-847f-4c7d-9152-5296e19946ce

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) (d : ℝ) (hg : 0 ≤ g (n+1)) : panjerStopLoss g n d ≤ panjerStopLoss g (n+1) d := by
  change (∑ k ∈ Finset.range (n + 1), max ((k : ℝ) - d) 0 * g k) ≤
    (∑ k ∈ Finset.range ((n + 1) + 1), max ((k : ℝ) - d) 0 * g k)
  calc
    (∑ k ∈ Finset.range (n + 1), max ((k : ℝ) - d) 0 * g k) ≤
        (∑ k ∈ Finset.range (n + 1), max ((k : ℝ) - d) 0 * g k) +
          max (((n + 1 : ℕ) : ℝ) - d) 0 * g (n + 1) := by
      apply le_add_of_nonneg_right
      exact mul_nonneg (le_max_right _ _) hg
    _ = (∑ k ∈ Finset.range ((n + 1) + 1), max ((k : ℝ) - d) 0 * g k) :=
      (Finset.sum_range_succ (fun k => max ((k : ℝ) - d) 0 * g k) (n + 1)).symm
