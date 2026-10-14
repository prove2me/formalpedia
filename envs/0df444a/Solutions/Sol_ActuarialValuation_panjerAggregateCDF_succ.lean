-- Prove2me | solution 1 for ActuarialValuation.panjerAggregateCDF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:07.599985+00:00
-- url     : https://prove2.me/submissions/b6bf3900-1d48-4206-a142-157ccbed330f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerAggregateCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g : ℕ → ℝ) (n : ℕ) : panjerAggregateCDF g (n+1) = panjerAggregateCDF g n + g (n+1) := by
  change (∑ k ∈ Finset.range ((n + 1) + 1), g k) =
    (∑ k ∈ Finset.range (n + 1), g k) + g (n + 1)
  exact Finset.sum_range_succ g (n + 1)
