-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_rho_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.637644+00:00
-- url     : https://prove2.me/submissions/cf2231ee-e498-4640-a0c2-ca87355f3e68

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r1 r2 a b : ℝ) (hr : r1 ≤ r2) (ha : 0 ≤ a) (hb : 0 ≤ b) : scrPairSquared r1 a b ≤ scrPairSquared r2 a b := by
  have hgap : 0 ≤ r2 - r1 := sub_nonneg.mpr hr
  have hprod : 0 ≤ (2:ℝ) * (r2-r1) * a * b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hgap) ha) hb
  unfold scrPairSquared scrCovarianceTerm
  nlinarith
