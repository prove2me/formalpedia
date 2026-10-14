-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateMean_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:54.585536+00:00
-- url     : https://prove2.me/submissions/659eaa5a-67b7-4f0b-b1d9-17e132350c2f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) : panjerAggregateMean g (n+1) = panjerAggregateMean g n + ((n+1 : ℕ) : ℝ) * g (n+1) := by
  change (∑ k ∈ Finset.range ((n + 1) + 1), (k : ℝ) * g k) =
    (∑ k ∈ Finset.range (n + 1), (k : ℝ) * g k) +
      (((n + 1 : ℕ) : ℝ) * g (n + 1))
  exact Finset.sum_range_succ (fun k => (k : ℝ) * g k) (n + 1)
