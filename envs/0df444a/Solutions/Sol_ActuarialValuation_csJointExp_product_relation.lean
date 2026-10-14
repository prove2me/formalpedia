-- Prove2me | solution 1 for ActuarialValuation.csJointExp_product_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:08:04.436996+00:00
-- url     : https://prove2.me/submissions/6a4ac645-52fb-4be2-9dd5-e4e0b77e9887

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointIndependentExp
import Definitions.Def_actuarial_csFirstExp
import Definitions.Def_actuarial_csMarginalOneExp
import Definitions.Def_actuarial_csMarginalTwoExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) :
    csJointIndependentExp a b c t =
      csFirstExp a b c t * Real.exp (-c*t) := by
  unfold csJointIndependentExp csMarginalOneExp csMarginalTwoExp csFirstExp
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
