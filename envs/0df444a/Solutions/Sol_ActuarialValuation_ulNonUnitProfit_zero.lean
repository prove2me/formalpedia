-- Prove2me | solution 1 for ActuarialValuation.ulNonUnitProfit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:26:09.740886+00:00
-- url     : https://prove2.me/submissions/e4a5b9d0-03e0-446e-af62-babb790b3902

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNonUnitProfit
open ActuarialValuation

theorem solution: ulNonUnitProfit 0 0 0 0 0=0 := by
  first
  | (simp [ulNonUnitProfit]; done)
  | (norm_num [ulNonUnitProfit]; done)
  | (unfold ulNonUnitProfit; positivity)
  | (simp only [ulNonUnitProfit]; positivity)
  | (unfold ulNonUnitProfit; ring)
  | (unfold ulNonUnitProfit; simp; done)
  | (unfold ulNonUnitProfit; norm_num; done)
  | (simp [ulNonUnitProfit]; ring)
  | (unfold ulNonUnitProfit; split_ifs <;> simp_all <;> linarith)
  | (unfold ulNonUnitProfit; nlinarith [sq_nonneg 0])
  | (simp_all [ulNonUnitProfit]; done)
  | (unfold ulNonUnitProfit; simp_all; done)
  | rfl
