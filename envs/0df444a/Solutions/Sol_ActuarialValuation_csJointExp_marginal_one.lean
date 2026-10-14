-- Prove2me | solution 1 for ActuarialValuation.csJointExp_marginal_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:05:36.119376+00:00
-- url     : https://prove2.me/submissions/16f22df7-1b05-4813-a410-523025a546a8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csMarginalOneExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c s : ℝ) (hs : 0 ≤ s) :
    csJointExp a b c s 0 = csMarginalOneExp a c s := by
  simp only [csJointExp, csMarginalOneExp,
    mul_zero, add_zero, max_eq_left hs]
  congr 1
  ring
