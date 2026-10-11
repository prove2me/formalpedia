-- Prove2me | solution 1 for ActuarialValuation.frTime_end
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:32:27.634297+00:00
-- url     : https://prove2.me/submissions/58be730c-ca8c-443d-abae-be84384d7544

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frTime
open ActuarialValuation

theorem solution(k m : ℕ) (hm : 0 < m) : frTime k m m = (k:ℝ)+1 := by
  unfold frTime
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_self hm0]
