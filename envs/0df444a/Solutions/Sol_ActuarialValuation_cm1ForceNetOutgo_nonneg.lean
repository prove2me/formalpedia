-- Prove2me | solution 1 for ActuarialValuation.cm1ForceNetOutgo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:34:06.845107+00:00
-- url     : https://prove2.me/submissions/6b40722a-1195-4297-a124-128d9fdf267d

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1ForceNetOutgo


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (μ B P : ℝ) (h : P ≤ μ*B) : 0 ≤ cm1ForceNetOutgo μ B P := by
  change 0 ≤ μ * B - P
  exact sub_nonneg.mpr h
