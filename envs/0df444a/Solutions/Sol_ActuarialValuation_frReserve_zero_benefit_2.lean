-- Prove2me | solution 2 for ActuarialValuation.frReserve_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:57.770166+00:00
-- url     : https://prove2.me/submissions/70a61475-fb8b-4be2-9ff3-ea51623c693f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution (assets premium q s growth endDiscount : ℝ) (hs : frUddSurvival q s ≠ 0) : frFractionalReserve assets premium 0 q s growth endDiscount * frUddSurvival q s = (assets+premium)*growth := by
  simp only [frFractionalReserve]
  simp [mul_zero, sub_zero]
  exact div_mul_cancel₀ ((assets + premium) * growth) hs

