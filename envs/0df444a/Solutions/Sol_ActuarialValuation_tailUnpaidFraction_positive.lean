-- Prove2me | solution 1 for ActuarialValuation.tailUnpaidFraction_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:56:32.800167+00:00
-- url     : https://prove2.me/submissions/f94aad85-4b45-4f26-9b8b-c74777f99112

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailUnpaidFraction
open ActuarialValuation

theorem solution(a : ℝ) (ha : a < 1) : 0 < tailUnpaidFraction a := by
  unfold tailUnpaidFraction
  linarith
