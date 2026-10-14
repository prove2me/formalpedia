-- Prove2me | solution 1 for ActuarialValuation.lcCohortLives_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:06.242245+00:00
-- url     : https://prove2.me/submissions/9842ac21-56dc-4d01-bee8-6e0fa3a168af

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival
import Definitions.Def_actuarial_lcCohortLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (q : ℕ → ℝ) (n : ℕ)
    (hi : 0 ≤ initial) (hq : 0 ≤ lcCohortSurvival q n) :
    0 ≤ lcCohortLives initial q n := by
  unfold lcCohortLives
  exact mul_nonneg hi hq
