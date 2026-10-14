-- Prove2me | solution 1 for ActuarialValuation.panjerSeverityMass_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:05:57.896843+00:00
-- url     : https://prove2.me/submissions/190444f7-3eda-4d64-a093-aacd0f81e0d9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerSeverityMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) : panjerSeverityMass f (n+1) = panjerSeverityMass f n + f (n+1) := by
  change (∑ j ∈ Finset.range ((n + 1) + 1), f j) =
    (∑ j ∈ Finset.range (n + 1), f j) + f (n + 1)
  exact Finset.sum_range_succ f (n + 1)
