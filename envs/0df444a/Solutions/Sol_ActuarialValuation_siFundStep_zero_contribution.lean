-- Prove2me | solution 1 for ActuarialValuation.siFundStep_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:08:29.482207+00:00
-- url     : https://prove2.me/submissions/77941154-5881-4ccc-9596-b36a83e4140a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep
open ActuarialValuation

theorem solution(fund gross : ℝ) : siFundStep fund 0 gross=fund*gross := by
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
