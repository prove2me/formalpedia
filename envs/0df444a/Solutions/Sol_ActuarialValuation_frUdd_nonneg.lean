-- Prove2me | solution 1 for ActuarialValuation.frUdd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T16:22:02.615586+00:00
-- url     : https://prove2.me/submissions/0ef21dbb-39a3-4a53-ab82-6a2f8f26e1cf

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival
open ActuarialValuation

theorem solution(q s : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ frUddSurvival q s := by
  unfold frUddSurvival
  nlinarith [mul_le_one₀ hs1 hq0 hq1]
