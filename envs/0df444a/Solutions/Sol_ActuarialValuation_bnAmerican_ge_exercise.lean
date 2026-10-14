-- Prove2me | solution 1 for ActuarialValuation.bnAmerican_ge_exercise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:00:39.997784+00:00
-- url     : https://prove2.me/submissions/877ad691-abfa-4c63-99d4-915fd5c96675

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exercise continuation : ℝ) : exercise ≤ bnAmericanNode exercise continuation := by
  unfold bnAmericanNode
  exact le_max_left _ _
