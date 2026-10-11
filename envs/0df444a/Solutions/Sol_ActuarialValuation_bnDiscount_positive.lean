-- Prove2me | solution 1 for ActuarialValuation.bnDiscount_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:04:07.367872+00:00
-- url     : https://prove2.me/submissions/aa73f1be-550c-4fda-b079-081e1be19b0b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnDiscount
open ActuarialValuation

theorem solution(R x : ℝ) (hR : 0 < R) (hx : 0 < x) : 0 < bnDiscount R x := by
  unfold bnDiscount
  exact div_pos hx hR
