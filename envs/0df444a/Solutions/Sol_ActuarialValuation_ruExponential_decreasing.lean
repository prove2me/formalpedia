-- Prove2me | solution 1 for ActuarialValuation.ruExponential_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:43:29.456185+00:00
-- url     : https://prove2.me/submissions/6c0f1597-ea71-4ff5-b96f-c73890cee189

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruExponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R x y : ℝ) (hR : 0 ≤ R) (hxy : x ≤ y) :
    ruExponential R y ≤ ruExponential R x := by
  unfold ruExponential
  apply Real.exp_le_exp.mpr
  have h : R * x ≤ R * y := mul_le_mul_of_nonneg_left hxy hR
  have e1 : (-R) * y = -(R * y) := by ring
  have e2 : (-R) * x = -(R * x) := by ring
  rw [e1, e2]
  exact neg_le_neg_iff.mpr h
