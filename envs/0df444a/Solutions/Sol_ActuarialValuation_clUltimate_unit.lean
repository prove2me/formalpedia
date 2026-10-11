-- Prove2me | solution 1 for ActuarialValuation.clUltimate_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:53:23.051982+00:00
-- url     : https://prove2.me/submissions/eb2478f6-9e73-49c3-ae60-33487e9ae212

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
open ActuarialValuation

theorem solution(p : ℝ) : clUltimate p 1 = p := by
  first
  | (simp [clUltimate]; done)
  | (norm_num [clUltimate]; done)
  | (unfold clUltimate; positivity)
  | (simp only [clUltimate]; positivity)
  | (unfold clUltimate; ring)
  | (unfold clUltimate; simp; done)
  | (unfold clUltimate; norm_num; done)
  | (simp [clUltimate]; ring)
  | (unfold clUltimate; split_ifs <;> simp_all <;> linarith)
  | (unfold clUltimate; nlinarith [sq_nonneg 0])
  | rfl
