-- Prove2me | solution 1 for AstrophysicalFluidDynamics.strong_shock_limit_ratios
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:46:39.410257+00:00
-- url     : https://prove2.me/submissions/bf7540cb-918f-4941-9ad4-e7d044b1e6ee

import Mathlib
import Definitions.Def_AstrophysicalFluidDynamics_ShockDefs

open AstrophysicalFluidDynamics Filter Topology in
theorem solution
    (γ : ℝ) (hγ : 1 < γ) :
    Tendsto (shockDensityRatio γ) atTop (𝓝 ((γ + 1) / (γ - 1))) ∧
    Tendsto (shockPressureRatio γ) atTop atTop ∧
    Tendsto (shockDownstreamMachSq γ) atTop (𝓝 ((γ - 1) / (2 * γ))) := by
  have hM2 : Tendsto (fun M : ℝ => M ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hinv : Tendsto (fun M : ℝ => (M ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hM2
  refine ⟨?_, ?_, ?_⟩
  · have h : Tendsto (fun M : ℝ => (γ + 1) / ((γ - 1) + 2 * (M ^ 2)⁻¹)) atTop
        (𝓝 ((γ + 1) / ((γ - 1) + 2 * 0))) := by
      refine tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) ?_
      rw [mul_zero, add_zero]; linarith
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have hM2pos : 0 < M ^ 2 := by positivity
    have hd : 0 < (γ - 1) * M ^ 2 + 2 := by nlinarith
    show (γ + 1) / ((γ - 1) + 2 * (M ^ 2)⁻¹) = (γ + 1) * M ^ 2 / ((γ - 1) * M ^ 2 + 2)
    rw [div_eq_div_iff (by positivity) hd.ne']
    field_simp
  · have h1 : Tendsto (fun M : ℝ => 2 * γ * M ^ 2) atTop atTop :=
      hM2.const_mul_atTop (by linarith)
    have h2 : Tendsto (fun M : ℝ => 2 * γ * M ^ 2 + (-(γ - 1))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ h1
    have h3 := h2.atTop_div_const (show (0:ℝ) < γ + 1 by linarith)
    refine h3.congr' ?_
    filter_upwards with M
    show (2 * γ * M ^ 2 + -(γ - 1)) / (γ + 1) = (2 * γ * M ^ 2 - (γ - 1)) / (γ + 1)
    ring
  · have h : Tendsto (fun M : ℝ => ((γ - 1) + 2 * (M ^ 2)⁻¹) / (2 * γ - (γ - 1) * (M ^ 2)⁻¹))
        atTop (𝓝 (((γ - 1) + 2 * 0) / (2 * γ - (γ - 1) * 0))) := by
      refine (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).div
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)) ?_
      rw [mul_zero, sub_zero]; linarith
    rw [mul_zero, add_zero, mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with M hM1
    have hM2pos : 1 < M ^ 2 := by nlinarith
    have hd : 0 < 2 * γ * M ^ 2 - (γ - 1) := by nlinarith
    have hinvlt : (M ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM2pos
    have hinvpos : 0 < (M ^ 2)⁻¹ := by positivity
    have hd2 : 0 < 2 * γ - (γ - 1) * (M ^ 2)⁻¹ := by nlinarith
    show ((γ - 1) + 2 * (M ^ 2)⁻¹) / (2 * γ - (γ - 1) * (M ^ 2)⁻¹)
      = (2 + (γ - 1) * M ^ 2) / (2 * γ * M ^ 2 - (γ - 1))
    rw [div_eq_div_iff hd2.ne' hd.ne']
    field_simp
    ring
