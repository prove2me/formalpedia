-- Prove2me | solution 1 for ActuarialValuation.srBound_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:23:09.276275+00:00
-- url     : https://prove2.me/submissions/54abae6e-efa7-4ecb-91ff-c7ad87541c54

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srLundbergBound
open ActuarialValuation

theorem solution(R u : ℝ) : 0<srLundbergBound R u := by
  first
  | (simp [srLundbergBound]; done)
  | (norm_num [srLundbergBound]; done)
  | (unfold srLundbergBound; positivity)
  | (simp only [srLundbergBound]; positivity)
  | (unfold srLundbergBound; ring)
  | (unfold srLundbergBound; simp; done)
  | (unfold srLundbergBound; norm_num; done)
  | (simp [srLundbergBound]; ring)
  | (unfold srLundbergBound; split_ifs <;> simp_all <;> linarith)
  | (unfold srLundbergBound; nlinarith [sq_nonneg 0])
  | (simp_all [srLundbergBound]; done)
  | (unfold srLundbergBound; simp_all; done)
  | rfl
