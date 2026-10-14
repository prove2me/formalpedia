-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_adjust_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T15:00:45.544585+00:00
-- url     : https://prove2.me/submissions/7eaf5820-636f-4e55-b6df-f4789f695aa1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerAdjustment
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 f0 : ℝ) (h0 : 0 < p0) (h1 : 0 ≤ p1) (hf : 0 ≤ f0) : 0 < cxPanjerAdjustment (cxPanjerA p0 p1) f0 := by
  have hd : 0 ≤ p1 / p0 := div_nonneg h1 (le_of_lt h0)
  have hprod : 0 ≤ (p1 / p0) * f0 := mul_nonneg hd hf
  unfold cxPanjerAdjustment cxPanjerA
  rw [neg_div]
  nlinarith
