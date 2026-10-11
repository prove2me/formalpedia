-- Prove2me | solution 1 for ActuarialValuation.cxBernCountPGF_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:36:17.146683+00:00
-- url     : https://prove2.me/submissions/0ec948e8-ecba-490d-b63c-4c29926f9c02

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernCountPGF
open ActuarialValuation

theorem solution(p0 p1 : ℝ) (h : p0+p1=1) : cxBernCountPGF p0 p1 1 = 1 := by
  unfold cxBernCountPGF
  linarith
