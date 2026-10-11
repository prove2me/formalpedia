-- Prove2me | solution 1 for ActuarialValuation.ulProfitNPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:20:41.540728+00:00
-- url     : https://prove2.me/submissions/09ce4fb4-f72b-49b0-a57c-78127c0d99e3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulProfitNPV
open ActuarialValuation

theorem solution(cash discount : ℕ → ℝ) : ulProfitNPV cash discount 0=0 := by
  simp [ulProfitNPV]
