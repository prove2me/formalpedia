-- Prove2me | solution 1 for ActuarialValuation.msMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:46:16.171884+00:00
-- url     : https://prove2.me/submissions/671e6a98-d4d4-48a1-ad7a-099a6ef1aa6d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
open ActuarialValuation

theorem solution(p : Fin 3 → ℝ) (h : ∀ i, p i=0) : msMass p = 0 := by
  simp [msMass, h]
