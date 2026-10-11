-- Prove2me | solution 1 for ActuarialValuation.commEffectiveDiscount_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:23:57.848693+00:00
-- url     : https://prove2.me/submissions/12f49436-9a0a-4ba1-acb9-164c2604777e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commEffectiveDiscount
open ActuarialValuation

theorem solution(v : ℝ) (h : v ≤ 1) : 0 ≤ commEffectiveDiscount v := by
  unfold commEffectiveDiscount
  linarith
