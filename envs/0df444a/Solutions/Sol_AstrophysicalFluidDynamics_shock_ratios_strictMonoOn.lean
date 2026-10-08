-- Prove2me | solution 1 for AstrophysicalFluidDynamics.shock_ratios_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:25:28.555883+00:00
-- url     : https://prove2.me/submissions/1829cfbe-c4a3-4f6b-8eaa-e9cbfab06045

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open Filter Topology

open AstrophysicalFluidDynamics in
theorem solution
    (γ : ℝ) (hγ : 1 < γ) :
    StrictMonoOn (shockDensityRatio γ) (Set.Ioi 0) ∧
    StrictMonoOn (shockPressureRatio γ) (Set.Ioi 0) := by
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    unfold shockDensityRatio
    have ha2 : 0 < a ^ 2 := by positivity
    have hab2 : a ^ 2 < b ^ 2 := by nlinarith
    have hd1 : 0 < (γ - 1) * a ^ 2 + 2 := by nlinarith
    have hd2 : 0 < (γ - 1) * b ^ 2 + 2 := by nlinarith
    rw [div_lt_div_iff₀ hd1 hd2]
    nlinarith
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    unfold shockPressureRatio
    have hab2 : a ^ 2 < b ^ 2 := by nlinarith
    have hg : 0 < γ + 1 := by linarith
    have hγ0 : 0 < γ := by linarith
    have hnum : 2 * γ * a ^ 2 - (γ - 1) < 2 * γ * b ^ 2 - (γ - 1) := by
      have := mul_lt_mul_of_pos_left hab2 (by linarith : (0:ℝ) < 2 * γ)
      linarith
    exact div_lt_div_of_pos_right hnum hg
