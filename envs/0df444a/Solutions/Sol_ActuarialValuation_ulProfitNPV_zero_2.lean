-- Prove2me | solution 2 for ActuarialValuation.ulProfitNPV_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.243212+00:00
-- url     : https://prove2.me/submissions/365ea7f0-8104-4686-8fdf-e9155ef8fbbe

import Mathlib
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulProfitNPV

open ActuarialValuation

theorem solution (cash discount : ℕ → ℝ) : ulProfitNPV cash discount 0=0 := by simp [ulProfitNPV]

