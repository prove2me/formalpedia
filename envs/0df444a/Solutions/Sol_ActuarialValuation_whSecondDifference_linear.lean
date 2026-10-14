-- Prove2me | solution 1 for ActuarialValuation.whSecondDifference_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:54:10.320982+00:00
-- url     : https://prove2.me/submissions/d2da5834-c94e-45d3-8aab-db22642d9d27

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whLinearCurve
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) (i : ℕ) : whSecondDifference (whLinearCurve a b) i = 0 := by
  simp only [whSecondDifference, whFirstDifference, whLinearCurve,
    Nat.cast_add, Nat.cast_one]
  ring
