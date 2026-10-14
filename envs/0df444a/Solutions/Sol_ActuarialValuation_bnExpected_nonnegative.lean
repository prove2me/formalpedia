-- Prove2me | solution 1 for ActuarialValuation.bnExpected_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:02.47979+00:00
-- url     : https://prove2.me/submissions/eccf785c-78d1-4698-bec4-3af42e1d0f5e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q xu xd : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hu : 0 ≤ xu) (hd : 0 ≤ xd) : 0 ≤ bnExpectedPayoff q xu xd := by
  unfold bnExpectedPayoff
  apply add_nonneg
  · exact mul_nonneg hq0 hu
  · exact mul_nonneg (sub_nonneg.mpr hq1) hd
