-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:31:38.430989+00:00
-- url     : https://prove2.me/submissions/321c7c23-0930-4374-b56a-cd2bcd77923e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
open ActuarialValuation

theorem solution(u c : ℝ) (x : ℕ → ℝ) : ruPathSurplus u c x 0 = u := by
  simp [ruPathSurplus, ruPremiumTotal, ruClaimTotal]
