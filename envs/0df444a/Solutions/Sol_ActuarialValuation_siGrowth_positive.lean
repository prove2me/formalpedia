-- Prove2me | solution 1 for ActuarialValuation.siGrowth_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:28:17.674115+00:00
-- url     : https://prove2.me/submissions/b271f2f0-796e-4d70-8dde-7cca0ac12e55

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrowth
open ActuarialValuation

theorem solution(i : ℝ) (h : -1 < i) : 0 < siGrowth i := by
  unfold siGrowth
  linarith
