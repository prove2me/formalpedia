-- Prove2me | solution 1 for ActuarialValuation.crPositivePart_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:24:47.382032+00:00
-- url     : https://prove2.me/submissions/8a37bcc7-1790-4f9b-b5f9-78309aa27a76

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crPositivePart
open ActuarialValuation

theorem solution(x : ℝ) (h : 0≤x) : crPositivePart x=x := by
  unfold crPositivePart
  exact max_eq_left h
