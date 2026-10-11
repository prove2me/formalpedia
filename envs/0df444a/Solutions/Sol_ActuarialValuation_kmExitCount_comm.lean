-- Prove2me | solution 1 for ActuarialValuation.kmExitCount_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:22:43.533745+00:00
-- url     : https://prove2.me/submissions/7ab942a0-5101-4a75-b3b6-92cf934893e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmExitCount
open ActuarialValuation

theorem solution(d c : ℝ) : kmExitCount d c = kmExitCount c d := by
  simp [kmExitCount, add_comm]
