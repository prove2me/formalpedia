-- Prove2me | solution 1 for ActuarialValuation.scrDiversificationSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:50.602114+00:00
-- url     : https://prove2.me/submissions/0b2f3c50-ce42-4bcd-ba12-c4230b207942

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiversificationSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) (hr : rho ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ scrDiversificationSquared rho a b := by
  have hgap : 0 ≤ 1-rho := sub_nonneg.mpr hr
  have hprod : 0 ≤ (2:ℝ) * (1-rho) * a * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hgap) ha) hb
  unfold scrDiversificationSquared scrSumSquared scrPairSquared scrCovarianceTerm
  nlinarith
