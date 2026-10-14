-- Prove2me | solution 1 for ActuarialValuation.bnAmerican_exercise_when_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:53.034461+00:00
-- url     : https://prove2.me/submissions/60edcb36-5a09-4cfe-a4c6-dec157aff0b1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exercise continuation : ℝ) (h : continuation ≤ exercise) : bnAmericanNode exercise continuation = exercise := by
  unfold bnAmericanNode
  exact max_eq_left h
