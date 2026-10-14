-- Prove2me | solution 1 for ActuarialValuation.kmSurvival_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:22.302566+00:00
-- url     : https://prove2.me/submissions/940d0b76-eb11-461b-9969-bf1e1f770177

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvivalFactor
import Definitions.Def_actuarial_kmSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) :
    kmSurvival r d (n+1) = kmSurvival r d n * kmSurvivalFactor (d n) (r n) := by
  simp [kmSurvival, Finset.prod_range_succ]
