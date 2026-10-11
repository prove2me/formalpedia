-- Prove2me | solution 1 for ActuarialValuation.kmRemainingRisk_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:21:32.124129+00:00
-- url     : https://prove2.me/submissions/7200154e-4911-4854-8deb-fe8191d8cead

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmRemainingRisk
open ActuarialValuation

theorem solution(r : ℝ) : kmRemainingRisk r 0 0 = r := by
  simp [kmRemainingRisk]
