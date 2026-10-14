-- Prove2me | solution 1 for ActuarialValuation.csJointExp_independent_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:45.989137+00:00
-- url     : https://prove2.me/submissions/e98f3021-5639-4986-bb47-6f25cfd5f216

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csMarginalOneExp
import Definitions.Def_actuarial_csMarginalTwoExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b s t : ℝ) :
    csJointExp a b 0 s t =
      csMarginalOneExp a 0 s * csMarginalTwoExp b 0 t := by
  unfold csJointExp csMarginalOneExp csMarginalTwoExp
  simp only [zero_mul, add_zero]
  rw [← Real.exp_add]
  congr 1
  ring
