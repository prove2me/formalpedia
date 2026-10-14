-- Prove2me | solution 1 for ActuarialValuation.whSecondDifference_shift
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:48:19.463191+00:00
-- url     : https://prove2.me/submissions/0497ee37-1802-4cbe-91aa-41cf391ef390

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whShiftedCurve
open ActuarialValuation

theorem solution(g : ℕ → ℝ) (i : ℕ) (s : ℝ) : whSecondDifference (fun j => whShiftedCurve g s j) i = whSecondDifference g i := by
  first
  | (simp [whSecondDifference, whFirstDifference, whShiftedCurve]; done)
  | (norm_num [whSecondDifference, whFirstDifference, whShiftedCurve]; done)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; positivity)
  | (simp only [whSecondDifference, whFirstDifference, whShiftedCurve]; positivity)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; ring)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; simp; done)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; norm_num; done)
  | (simp [whSecondDifference, whFirstDifference, whShiftedCurve]; ring)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; split_ifs <;> simp_all <;> linarith)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; nlinarith [sq_nonneg 0])
  | (simp_all [whSecondDifference, whFirstDifference, whShiftedCurve]; done)
  | (unfold whSecondDifference whFirstDifference whShiftedCurve; simp_all; done)
  | rfl
