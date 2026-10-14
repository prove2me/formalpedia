-- Prove2me | solution 1 for ActuarialValuation.lcCohortLives_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:08.049678+00:00
-- url     : https://prove2.me/submissions/0e217e89-d897-4697-86a3-5ff4492c02c7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (initial : ℝ) (q : ℕ → ℝ) :
    lcCohortLives initial q 0 = initial := by
  simp [lcCohortLives, lcCohortSurvival]
