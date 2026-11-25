-- Prove2me | solution 1 for Arxiv0709_3003.eq5_band_averaged_cbe
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T18:30:18.864793+00:00
-- url     : https://prove2.me/submissions/ac485adb-ee95-4772-b302-5bfb59177468

import Definitions.Def_Arxiv0709_3003_Basic
import Theorems.Thm_Arxiv0709_3003_eq5_single_frequency_cbe

open MeasureTheory ProbabilityTheory Filter Topology Arxiv0709_3003

private lemma besselJ0_zero : besselJ0 0 = 1 := by
  simp [besselJ0, Real.pi_ne_zero]

private lemma continuous_besselJ0 : Continuous besselJ0 := by
  unfold besselJ0
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x θ : ℝ => Real.cos (x * Real.sin θ)) (by fun_prop) 0 Real.pi

private lemma tendsto_besselJ0_sq_atTop :
    Tendsto (fun x : ℝ => besselJ0 x ^ 2) atTop (𝓝 0) := by
  have h0 := eq5_single_frequency_cbe 1 one_pos 1 (2 * Real.pi) 1 0
    one_pos Real.two_pi_pos one_pos
  have hlim : Tendsto (fun x : ℝ => meanSqCorr 1 1 (2 * Real.pi) 1 x) atTop (𝓝 3) := by
    simpa using h0.1
  have hrel : ∀ x : ℝ, besselJ0 x ^ 2 = (meanSqCorr 1 1 (2 * Real.pi) 1 x / 3 - 1) / 2 := by
    intro x
    have hx := (eq5_single_frequency_cbe 1 one_pos 1 (2 * Real.pi) 1 x
      one_pos Real.two_pi_pos one_pos).2
    have harg : 2 * Real.pi * 1 * x / (2 * Real.pi) = x := by
      field_simp [Real.two_pi_pos.ne']
    rw [harg, cbeSpatial, hlim.limUnder_eq] at hx
    linarith
  have h1 : Tendsto (fun x : ℝ => (meanSqCorr 1 1 (2 * Real.pi) 1 x / 3 - 1) / 2)
      atTop (𝓝 ((3 / 3 - 1) / 2)) :=
    (((hlim.div_const 3).sub_const 1).div_const 2)
  have hval : ((3 : ℝ) / 3 - 1) / 2 = 0 := by norm_num
  rw [hval] at h1
  exact h1.congr (fun x => (hrel x).symm)

theorem solution (N : ℕ) (hN : 0 < N) (s c f bw : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hbw : 0 < bw) (hband : bw / 2 < f) :
    (∀ r : ℝ, cbeBandAvg N s c f bw r =
      (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
        (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2)) ∧
    cbeBandAvg N s c f bw 0 = 3 ∧
    Tendsto (fun r => cbeBandAvg N s c f bw r) atTop (𝓝 1) := by
  have hab : f - bw / 2 ≤ f + bw / 2 := by linarith
  have hfl : 0 < f - bw / 2 := sub_pos.mpr hband
  have hformula : ∀ r : ℝ, cbeBandAvg N s c f bw r =
      (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
        (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) := by
    intro r
    rw [cbeBandAvg]
    congr 1
    refine intervalIntegral.integral_congr fun f' hf' => ?_
    rw [Set.uIcc_of_le hab] at hf'
    have hf'_pos : 0 < f' := lt_of_lt_of_le hfl hf'.1
    exact (eq5_single_frequency_cbe N hN s c f' r hs hc hf'_pos).2
  refine ⟨hformula, ?_, ?_⟩
  · rw [hformula 0]
    simp only [mul_zero, zero_div, besselJ0_zero, one_pow, mul_one]
    norm_num [intervalIntegral.integral_const]
    field_simp [hbw.ne']
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hsq := (Metric.tendsto_atTop.mp tendsto_besselJ0_sq_atTop) (ε / 4) (by positivity)
    rcases hsq with ⟨X, hX⟩
    set R : ℝ := max 0 (X * c / (2 * Real.pi * (f - bw / 2)))
    refine ⟨R, fun r hr => ?_⟩
    have hr_nn : 0 ≤ r := le_trans (le_max_left _ _) hr
    have hr_X : X * c / (2 * Real.pi * (f - bw / 2)) ≤ r := le_trans (le_max_right _ _) hr
    rw [hformula r, Real.dist_eq]
    have hcont : Continuous (fun f' : ℝ =>
        1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) := by
      refine continuous_const.add (continuous_const.mul ((continuous_besselJ0.comp ?_).pow 2))
      fun_prop
    have hlo : ∫ _f' in (f - bw / 2)..(f + bw / 2), (1 : ℝ) ≤
        ∫ f' in (f - bw / 2)..(f + bw / 2),
          (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) := by
      refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (hcont.intervalIntegrable _ _) fun f' _ => ?_
      nlinarith [sq_nonneg (besselJ0 (2 * Real.pi * f' * r / c))]
    have hhi : ∫ f' in (f - bw / 2)..(f + bw / 2),
          (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) ≤
        ∫ _f' in (f - bw / 2)..(f + bw / 2), (1 + ε / 2) := by
      refine intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
        intervalIntegrable_const fun f' hf' => ?_
      have harg : X ≤ 2 * Real.pi * f' * r / c := by
        have h1 : X * c ≤ 2 * Real.pi * (f - bw / 2) * r := by
          have := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * (f - bw / 2))).mp hr_X
          linarith
        have h2 : 2 * Real.pi * (f - bw / 2) * r ≤ 2 * Real.pi * f' * r := by
          have : 0 ≤ 2 * Real.pi * r := by positivity
          nlinarith [hf'.1]
        exact (le_div_iff₀ hc).mpr (h1.trans h2)
      have hsmall := hX (2 * Real.pi * f' * r / c) harg
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hsmall
      linarith
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
    have hlen : (f + bw / 2) - (f - bw / 2) = bw := by ring
    rw [hlen] at hlo hhi
    have hge1 : 1 ≤ (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
        (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) := by
      calc (1 : ℝ) = (1 / bw) * (bw * 1) := by field_simp [hbw.ne']
        _ ≤ (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
              (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) := by gcongr
    have hle1 : (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
        (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2) ≤ 1 + ε / 2 := by
      calc (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2),
            (1 + 2 * besselJ0 (2 * Real.pi * f' * r / c) ^ 2)
          ≤ (1 / bw) * (bw * (1 + ε / 2)) := by gcongr
        _ = 1 + ε / 2 := by field_simp [hbw.ne']
    rw [abs_of_nonneg (sub_nonneg.mpr hge1)]
    linarith
