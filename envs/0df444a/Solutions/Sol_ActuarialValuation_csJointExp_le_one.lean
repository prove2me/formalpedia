-- Prove2me | solution 1 for ActuarialValuation.csJointExp_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:09:07.208498+00:00
-- url     : https://prove2.me/submissions/15c0d2d0-9442-4d35-ae90-a8ae61acee0e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c s t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    csJointExp a b c s t ≤ 1 := by
  have hmax : 0 ≤ max s t :=
    le_trans hs (le_max_left s t)
  have hsum : 0 ≤ a*s + b*t + c*max s t :=
    add_nonneg (add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht))
      (mul_nonneg hc hmax)
  unfold csJointExp
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr hsum)
