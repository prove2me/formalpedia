-- Prove2me | solution 1 for ActuarialValuation.bnAmerican_wait_when_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:06.248434+00:00
-- url     : https://prove2.me/submissions/d5a72b85-821d-4bad-9986-22c56a0fe734

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exercise continuation : ℝ) (h : exercise ≤ continuation) : bnAmericanNode exercise continuation = continuation := by
  unfold bnAmericanNode
  exact max_eq_right h
