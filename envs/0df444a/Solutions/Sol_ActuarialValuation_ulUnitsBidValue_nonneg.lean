-- Prove2me | solution 1 for ActuarialValuation.ulUnitsBidValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:29:11.724281+00:00
-- url     : https://prove2.me/submissions/89a7fe69-2223-49c0-a259-82cf2ed66fd1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulUnitsBidValue
open ActuarialValuation

theorem solution(units bid : ℝ) (hu : 0 ≤ units) (hb : 0 ≤ bid) : 0 ≤ ulUnitsBidValue units bid := by
  first
  | (simp [ulUnitsBidValue]; done)
  | (norm_num [ulUnitsBidValue]; done)
  | (unfold ulUnitsBidValue; positivity)
  | (simp only [ulUnitsBidValue]; positivity)
  | (unfold ulUnitsBidValue; ring)
  | (unfold ulUnitsBidValue; simp; done)
  | (unfold ulUnitsBidValue; norm_num; done)
  | (simp [ulUnitsBidValue]; ring)
  | (unfold ulUnitsBidValue; split_ifs <;> simp_all <;> linarith)
  | (unfold ulUnitsBidValue; nlinarith [sq_nonneg 0])
  | (simp_all [ulUnitsBidValue]; done)
  | (unfold ulUnitsBidValue; simp_all; done)
  | rfl
