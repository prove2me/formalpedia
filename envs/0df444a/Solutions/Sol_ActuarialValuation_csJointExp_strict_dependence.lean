-- Prove2me | solution 1 for ActuarialValuation.csJointExp_strict_dependence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:12:25.444046+00:00
-- url     : https://prove2.me/submissions/e0a28bdd-fd15-4c53-bbe9-1fdc08f270f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csJointIndependentExp
import Definitions.Def_actuarial_csMarginalOneExp
import Definitions.Def_actuarial_csMarginalTwoExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    csJointIndependentExp a b c t < csJointExp a b c t t := by
  unfold csJointIndependentExp csMarginalOneExp csMarginalTwoExp csJointExp
  rw [← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  simp only [max_self]
  nlinarith [mul_pos hc ht]
