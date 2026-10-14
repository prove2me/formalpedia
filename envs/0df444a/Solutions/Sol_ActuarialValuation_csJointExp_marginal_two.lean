-- Prove2me | solution 1 for ActuarialValuation.csJointExp_marginal_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:07:28.713807+00:00
-- url     : https://prove2.me/submissions/58aae6db-0aca-4460-9084-9b2b28821b62

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csMarginalTwoExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) (ht : 0 ≤ t) :
    csJointExp a b c 0 t = csMarginalTwoExp b c t := by
  simp only [csJointExp, csMarginalTwoExp,
    zero_mul, zero_add, max_eq_right ht]
  congr 1
  ring
