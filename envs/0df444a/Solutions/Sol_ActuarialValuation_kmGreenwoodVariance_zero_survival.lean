-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodVariance_zero_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:22:42.043984+00:00
-- url     : https://prove2.me/submissions/6dfc3f6a-a5bd-43ec-b1c5-b4c4dfeddd77

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmGreenwoodVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) (h : kmSurvival r d n = 0) :
    kmGreenwoodVariance r d n = 0 := by
  simp [kmGreenwoodVariance, h]
