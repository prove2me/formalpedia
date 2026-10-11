-- Prove2me | solution 1 for ActuarialValuation.pvLoading_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:24:59.03796+00:00
-- url     : https://prove2.me/submissions/775d23d6-467b-419c-a543-62d77fdb9a95

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoading
open ActuarialValuation

theorem solution(equivalence : ℝ) : pvLoading equivalence equivalence = 0 := by
  simp [pvLoading]
