-- Prove2me | solution 1 for ActuarialValuation.bdDuration_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:09:24.597544+00:00
-- url     : https://prove2.me/submissions/3e94d87a-bc2b-4ed7-828b-e6b9891fb3e3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdDurationNumerator
open ActuarialValuation

theorem solution(D c : ℕ → ℝ) : bdDurationNumerator D c 0 = 0 := by
  simp [bdDurationNumerator]
