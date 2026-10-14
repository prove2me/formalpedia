-- Prove2me | solution 1 for ActuarialValuation.scrCovarianceTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:36:02.782781+00:00
-- url     : https://prove2.me/submissions/a512b260-af63-4e37-bad6-9abc9c55f8a8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCovarianceTerm

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rho a b : ℝ) (hr : 0 ≤ rho) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ scrCovarianceTerm rho a b := by
  unfold scrCovarianceTerm
  exact mul_nonneg (mul_nonneg hr ha) hb
