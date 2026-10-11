-- Prove2me | solution 1 for ActuarialValuation.kmCensorHazard_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:33.226757+00:00
-- url     : https://prove2.me/submissions/ed29ea91-9cda-49b6-88fb-ba688125aa67

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmCensorHazard
open ActuarialValuation

theorem solution(r : ℝ) : kmCensorHazard 0 r = 0 := by
  first
  | (simp [kmCensorHazard]; done)
  | (norm_num [kmCensorHazard]; done)
  | (unfold kmCensorHazard; positivity)
  | (simp only [kmCensorHazard]; positivity)
  | (unfold kmCensorHazard; ring)
  | (unfold kmCensorHazard; simp; done)
  | (unfold kmCensorHazard; norm_num; done)
  | (simp [kmCensorHazard]; ring)
  | (unfold kmCensorHazard; split_ifs <;> simp_all <;> linarith)
  | (unfold kmCensorHazard; nlinarith [sq_nonneg 0])
  | (simp_all [kmCensorHazard]; done)
  | (unfold kmCensorHazard; simp_all; done)
  | rfl
