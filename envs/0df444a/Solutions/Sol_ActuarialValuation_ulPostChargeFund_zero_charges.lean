-- Prove2me | solution 1 for ActuarialValuation.ulPostChargeFund_zero_charges
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:33:22.215226+00:00
-- url     : https://prove2.me/submissions/e7b7c48d-4a0c-414b-8f44-43a73e19db07

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPostChargeFund
open ActuarialValuation

theorem solution(fund : ℝ) : ulPostChargeFund fund 0 0=fund := by
  simp [ulPostChargeFund, ulCharge]
