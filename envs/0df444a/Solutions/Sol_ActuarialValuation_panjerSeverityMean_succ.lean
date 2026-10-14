-- Prove2me | solution 1 for ActuarialValuation.panjerSeverityMean_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:04.308356+00:00
-- url     : https://prove2.me/submissions/846ab79e-f2e2-45a9-be64-3e842f3d2981

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) : panjerSeverityMean f (n+1) = panjerSeverityMean f n + ((n+1 : ℕ) : ℝ) * f (n+1) := by
  change (∑ j ∈ Finset.range ((n + 1) + 1), (j : ℝ) * f j) =
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) * f j) +
      (((n + 1 : ℕ) : ℝ) * f (n + 1))
  exact Finset.sum_range_succ (fun j => (j : ℝ) * f j) (n + 1)
