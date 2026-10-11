-- Prove2me | solution 1 for ActuarialValuation.ratExposureSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:06:36.068066+00:00
-- url     : https://prove2.me/submissions/55aabc22-407a-4854-9f06-b12706194c77

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratExposureSum
open ActuarialValuation

theorem solution(e : ℕ → ℝ) : ratExposureSum e 0 = 0 := by
  first
  | (simp [ratExposureSum]; done)
  | (norm_num [ratExposureSum]; done)
  | (unfold ratExposureSum; positivity)
  | (simp only [ratExposureSum]; positivity)
  | (unfold ratExposureSum; ring)
  | (unfold ratExposureSum; simp; done)
  | (unfold ratExposureSum; norm_num; done)
  | (simp [ratExposureSum]; ring)
  | (unfold ratExposureSum; split_ifs <;> simp_all <;> linarith)
  | (unfold ratExposureSum; nlinarith [sq_nonneg 0])
  | (simp_all [ratExposureSum]; done)
  | (unfold ratExposureSum; simp_all; done)
  | rfl
