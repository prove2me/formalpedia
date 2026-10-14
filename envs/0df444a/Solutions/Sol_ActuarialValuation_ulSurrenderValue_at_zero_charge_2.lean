-- Prove2me | solution 2 for ActuarialValuation.ulSurrenderValue_at_zero_charge
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:42.379454+00:00
-- url     : https://prove2.me/submissions/c3aa9b4d-ec3f-4a26-9096-002be582fe8a

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulSurrenderValue

open ActuarialValuation

theorem solution (fund : ℝ) (hf : 0≤fund) : ulSurrenderValue fund 0=fund := by simp [ulSurrenderValue, max_eq_right hf]

