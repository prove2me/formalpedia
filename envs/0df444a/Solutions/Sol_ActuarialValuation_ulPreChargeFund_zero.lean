-- Prove2me | solution 1 for ActuarialValuation.ulPreChargeFund_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:26:02.546769+00:00
-- url     : https://prove2.me/submissions/cc1067a5-3087-4c2f-944f-d8baa1fd97e8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPreChargeFund
open ActuarialValuation

theorem solution(fund alloc : ℝ) : ulPreChargeFund fund alloc 0=fund+alloc := by
  simp [ulPreChargeFund]
