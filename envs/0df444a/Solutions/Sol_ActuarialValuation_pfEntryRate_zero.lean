-- Prove2me | solution 1 for ActuarialValuation.pfEntryRate_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:53:55.744001+00:00
-- url     : https://prove2.me/submissions/8c2e7d4f-612b-4de7-8c1a-afc72eaf0b6b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryRate
open ActuarialValuation

theorem solution(p : ℝ) (hp : p≠0) : pfEntryRate 0 p=0 := by
  first
  | (simp [pfEntryRate]; done)
  | (norm_num [pfEntryRate]; done)
  | (unfold pfEntryRate; positivity)
  | (simp only [pfEntryRate]; positivity)
  | (unfold pfEntryRate; ring)
  | (unfold pfEntryRate; simp; done)
  | (unfold pfEntryRate; norm_num; done)
  | (simp [pfEntryRate]; ring)
  | (unfold pfEntryRate; split_ifs <;> simp_all <;> linarith)
  | (unfold pfEntryRate; nlinarith [sq_nonneg 0])
  | (simp_all [pfEntryRate]; done)
  | (unfold pfEntryRate; simp_all; done)
  | rfl
