-- Prove2me | solution 1 for ActuarialValuation.csFirstExp_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:11:21.623684+00:00
-- url     : https://prove2.me/submissions/31666fbb-c861-4d92-bce0-29db45622ec2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c s t : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hst : s ≤ t) :
    csFirstExp a b c t ≤ csFirstExp a b c s := by
  have hsum : 0 ≤ a+b+c := add_nonneg (add_nonneg ha hb) hc
  unfold csFirstExp
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr hsum))
