-- Prove2me | solution 1 for ActuarialValuation.siGrowth_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:41:55.229602+00:00
-- url     : https://prove2.me/submissions/68cc3495-01d9-428a-8635-62f0c3986b02

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrowth
open ActuarialValuation

theorem solution: siGrowth 0=1 := by
  first
  | (simp [siGrowth]; done)
  | (norm_num [siGrowth]; done)
  | (unfold siGrowth; positivity)
  | (simp only [siGrowth]; positivity)
  | (unfold siGrowth; ring)
  | (unfold siGrowth; simp; done)
  | (unfold siGrowth; norm_num; done)
  | (simp [siGrowth]; ring)
  | (unfold siGrowth; split_ifs <;> simp_all <;> linarith)
  | (unfold siGrowth; nlinarith [sq_nonneg 0])
  | rfl
