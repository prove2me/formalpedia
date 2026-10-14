-- Prove2me | solution 1 for ActuarialValuation.siFundStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:34:10.172359+00:00
-- url     : https://prove2.me/submissions/0cd907fd-a85a-4510-a035-b53c00a6c9c0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep
open ActuarialValuation

theorem solution(fund contribution : ℝ) : siFundStep fund contribution 1=fund+contribution := by
  first
  | (simp [siFundStep]; done)
  | (norm_num [siFundStep]; done)
  | (unfold siFundStep; positivity)
  | (simp only [siFundStep]; positivity)
  | (unfold siFundStep; ring)
  | (unfold siFundStep; simp; done)
  | (unfold siFundStep; norm_num; done)
  | (simp [siFundStep]; ring)
  | (unfold siFundStep; split_ifs <;> simp_all <;> linarith)
  | (unfold siFundStep; nlinarith [sq_nonneg 0])
  | (simp_all [siFundStep]; done)
  | (unfold siFundStep; simp_all; done)
  | rfl
