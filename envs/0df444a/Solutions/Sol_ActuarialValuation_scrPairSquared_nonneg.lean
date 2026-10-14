-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:28.187934+00:00
-- url     : https://prove2.me/submissions/b01386bb-5f63-4215-ad38-293f58e4a93c

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) (hr : 0 ≤ rho) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ scrPairSquared rho a b := by
  unfold scrPairSquared scrCovarianceTerm
  have hc : 0 ≤ rho * a * b := mul_nonneg (mul_nonneg hr ha) hb
  have htwo : 0 ≤ (2:ℝ) * (rho * a * b) :=
    mul_nonneg (by norm_num) hc
  nlinarith [sq_nonneg a, sq_nonneg b]
