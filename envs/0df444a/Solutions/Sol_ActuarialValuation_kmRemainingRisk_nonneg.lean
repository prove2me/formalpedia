-- Prove2me | solution 1 for ActuarialValuation.kmRemainingRisk_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:28:42.591267+00:00
-- url     : https://prove2.me/submissions/f1f6820a-fe89-4143-af07-2ffac07c740a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRemainingRisk
import Definitions.Def_actuarial_kmExitCount
open ActuarialValuation

theorem solution(r d c : ℝ) (h : kmExitCount d c ≤ r) : 0 ≤ kmRemainingRisk r d c := by
  unfold kmRemainingRisk
  unfold kmExitCount at h
  linarith
