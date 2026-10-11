-- Prove2me | solution 1 for ActuarialValuation.pfAssetsNext_zero_flow
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:14:22.127918+00:00
-- url     : https://prove2.me/submissions/89bb68a2-e574-4d09-921a-41186efb254d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAssetsNext
open ActuarialValuation

theorem solution(a : ℝ) : pfAssetsNext a 0 0 0 0=a := by
  first
  | (simp [pfAssetsNext]; done)
  | (norm_num [pfAssetsNext]; done)
  | (unfold pfAssetsNext; positivity)
  | (simp only [pfAssetsNext]; positivity)
  | (unfold pfAssetsNext; ring)
  | (unfold pfAssetsNext; simp; done)
  | (unfold pfAssetsNext; norm_num; done)
  | (simp [pfAssetsNext]; ring)
  | (unfold pfAssetsNext; split_ifs <;> simp_all <;> linarith)
  | (unfold pfAssetsNext; nlinarith [sq_nonneg 0])
  | (simp_all [pfAssetsNext]; done)
  | (unfold pfAssetsNext; simp_all; done)
  | rfl
