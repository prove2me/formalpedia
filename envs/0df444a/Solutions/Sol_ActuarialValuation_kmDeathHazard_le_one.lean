-- Prove2me | solution 1 for ActuarialValuation.kmDeathHazard_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:37:31.728034+00:00
-- url     : https://prove2.me/submissions/3bf9fb62-3b14-4a93-b3e4-4c141e91514f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmDeathHazard
open ActuarialValuation

theorem solution(d r : ℝ) (hd : d ≤ r) (hr : 0 < r) : kmDeathHazard d r ≤ 1 := by
  unfold kmDeathHazard
  exact (div_le_one hr).2 hd
