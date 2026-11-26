-- Prove2me | Definitions.Def_RHHeight1000_20261117_P02_v3
-- name    : RHHeight1000_20261117_P02_v3
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:07:00.107519+00:00
-- url     : https://prove2.me/theorems/fe813758-0eb6-48d3-9fc7-bef6171c952d
-- title:
--   Zeta analytic counting dependencies 02 (ordinary proofs)
-- statement:
--   Complete analytic proof dependencies for zeta counting, without custom metaprogramming declarations. No numeric zero-certification assumptions. Source attribution and Apache-2.0 headers retained.
-- source:
--   smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe; reduced height and Lean 4.33.1 packaging by Desenvolvimento RH. AXLE full source d2dcb520-c50a-44dc-a527-de0f7a51b892.

import Definitions.Def_RHHeight1000_20261117_P01_v3
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort19
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory Set
private lemma norm_sub_one_le_norm_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖z - 1‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [hz]
theorem norm_Gamma_le_strip_quarter_two :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℂ, (1 : ℝ) / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.Gamma w‖ ≤ C₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
  obtain ⟨c₁, c₂, hc₁, hc₁₂, H⟩ :=
    norm_Gamma_vertical_le (a := 1 / 4) (b := 2) (by norm_num) (by norm_num)
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_Icc (a := (1 / 4 : ℝ)) (b := 2)).reProdIm
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      fun w hw ↦ (differentiableAt_Gamma_of_re_pos (by
        rw [mem_reProdIm] at hw; linarith [hw.1.1])).continuousAt.continuousWithinAt
  refine ⟨max c₂ M₀, lt_of_lt_of_le hc₂ (le_max_left _ _), fun w hw1 hw2 ↦ ?_⟩
  have hnormnn : (0 : ℝ) ≤ ‖w‖ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hC₀ : (0 : ℝ) ≤ max c₂ M₀ := hc₂.le.trans (le_max_left _ _)
  by_cases himw : 1 ≤ |w.im|
  ·
    have hexp : Real.exp (-(Real.pi / 2) * |w.im|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg w.im)])
    have hrpow : |w.im| ^ (w.re - 1 / 2) ≤ ‖w‖ ^ ((3 : ℝ) / 2) :=
      (Real.rpow_le_rpow_of_exponent_le himw (by linarith)).trans
        (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm w) (by norm_num))
    have hub := (H w.re hw1 hw2 w.im himw).2
    rw [Complex.re_add_im] at hub
    calc ‖Complex.Gamma w‖
        ≤ c₂ * |w.im| ^ (w.re - 1 / 2) * Real.exp (-(Real.pi / 2) * |w.im|) := hub
      _ ≤ c₂ * ‖w‖ ^ ((3 : ℝ) / 2) * 1 := by gcongr
      _ ≤ max c₂ M₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
            nlinarith [mul_le_mul_of_nonneg_right (le_max_left c₂ M₀) hnormnn]
  ·
    have hwK := hM₀ w (by
      rw [mem_reProdIm]
      exact ⟨⟨hw1, hw2⟩, (abs_lt.mp (not_le.mp himw)).1.le, (abs_lt.mp (not_le.mp himw)).2.le⟩)
    nlinarith [le_max_right c₂ M₀]
theorem norm_Gamma_le_exp_halfplane :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ Real.exp (Cγ * (‖z‖ * Real.log ‖z‖ + 1)) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := norm_Gamma_le_strip_quarter_two
  have aux : ∀ n : ℕ, ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → z.re ≤ 2 + n → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n := by
    intro n
    induction n with
    | zero => exact fun z hz1 hz2 _ ↦ by simpa using hstrip z hz1 (by simpa using hz2)
    | succ n ih =>
        intro z hz1 hz2 hz3
        by_cases hcase : z.re ≤ 2 + n
        · exact (ih z hz1 hcase hz3).trans (by gcongr; exact Nat.le_succ n)
        · have hrebig : (2 : ℝ) < z.re :=
            lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg n)) (not_le.mp hcase)
          have hwre : (z - 1).re = z.re - 1 := by simp
          have hwne : z - 1 ≠ 0 := fun hh ↦ by rw [hh, Complex.zero_re] at hwre; linarith
          have hstep : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
            rw [← Complex.Gamma_add_one (z - 1) hwne]; congr 1; ring
          have hw_norm1 : (1 : ℝ) ≤ ‖z - 1‖ :=
            le_trans (by rw [hwre]; linarith)
              ((le_abs_self _).trans (abs_re_le_norm (z - 1)))
          have hih := ih (z - 1) (by rw [hwre]; linarith)
            (by rw [hwre]; push_cast at hz2 ⊢; linarith) hw_norm1
          have hnorm_le : ‖z - 1‖ ≤ ‖z‖ := norm_sub_one_le_norm_of_half_le_re (by linarith)
          rw [hstep, norm_mul, pow_succ]
          calc ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖
              ≤ ‖z‖ * (C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n) :=
                mul_le_mul hnorm_le (hih.trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
            _ = C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * (‖z‖ ^ n * ‖z‖) := by ring
  refine ⟨max (5 / 2) (Real.log (2 * C₀)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz1 hz3 ↦ ?_⟩
  set N := ‖z‖ with hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hz3
  have hL0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hz3
  have hNL : (0 : ℝ) ≤ N * Real.log N := mul_nonneg hN0.le hL0
  set n := ⌊z.re⌋₊ with hn
  have hn_le : (n : ℝ) ≤ N :=
    (Nat.floor_le (by linarith)).trans ((le_abs_self _).trans (abs_re_le_norm z))
  have hbase := aux n z hz1 (by linarith [Nat.lt_floor_add_one z.re]) hz3
  rw [← hN] at hbase
  have h1le : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := Real.one_le_rpow hz3 (by norm_num)
  have hpow : N ^ n ≤ Real.exp (N * Real.log N) := by
    rw [← Real.rpow_natCast N n, Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn_le hL0])
  have hkey : C₀ * (1 + N ^ ((3 : ℝ) / 2)) * N ^ n
      ≤ Real.exp (Real.log (2 * C₀) + Real.log N * (3 / 2)) * Real.exp (N * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_def_of_pos hN0]
    exact mul_le_mul (by nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr h1le)]) hpow
      (by positivity) (by positivity)
  refine (hbase.trans hkey).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hCγ1 : (5 : ℝ) / 2 ≤ max (5 / 2) (Real.log (2 * C₀)) := le_max_left _ _
  nlinarith [le_max_right (5 / 2 : ℝ) (Real.log (2 * C₀)), hNL,
    mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) hL0, mul_nonneg (sub_nonneg.mpr hCγ1) hNL]
theorem norm_riemannZeta_sub_head_le {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ Real.sqrt 2 * ‖s‖ := by
  have hσpos : 0 < s.re := by linarith
  have key := ZetaBnd_aux1b 2 (by norm_num) (σ := s.re) (t := s.im) hσpos
  simp only [Nat.cast_ofNat, Complex.re_add_im] at key
  have hb2 : (2 : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt 2 := by
    calc (2 : ℝ) ^ (-s.re) / s.re = (2 : ℝ) ^ (-s.re) * (1 / s.re) := by ring
      _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) * 2 :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
            (by rw [div_le_iff₀ hσpos]; linarith) (by positivity)
            (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = Real.sqrt 2 := by
          rw [mul_comm]; nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]; congr 1; norm_num
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (key.trans hb2) (norm_nonneg s)
theorem norm_riemannZeta_le_const_mul_of_half_le_re :
    ∃ Cζ : ℝ, 0 < Cζ ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ → ‖riemannZeta s‖ ≤ Cζ * ‖s‖ := by
  refine ⟨5 + Real.sqrt 2, by positivity, fun s hs hsnorm ↦ ?_⟩
  have hσpos : 0 < s.re := by linarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
  by_cases hcase : 2 ≤ s.re
  ·
    have hb := norm_riemannZeta_sub_one_le_of_two_le_re hcase
    have h2 := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at h2
    nlinarith [Real.sqrt_nonneg 2, Real.pi_le_four, Real.pi_pos,
      mul_nonneg (Real.sqrt_nonneg 2) (by linarith : (0 : ℝ) ≤ ‖s‖)]
  ·
    have hs0 : s ≠ 0 := by rintro rfl; simp at hσpos
    have hexp : riemannZeta s
        = (∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s)
          + (-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)
          + (-(((2 : ℕ) : ℂ) ^ (-s))) / 2
          + s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) :=
      (Zeta0EqZeta (N := 2) (by norm_num) hσpos hs1).symm
    have hA : ‖∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s‖ ≤ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_cpow hs0, Complex.one_cpow,
        div_zero, div_one, zero_add]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_one, norm_natCast_cpow_of_pos (by norm_num : 0 < 2)]
      have hden : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ s.re := by positivity
      linarith [(div_le_one hden).mpr (Real.one_le_rpow (by norm_num) (by linarith))]
    have hB : ‖(-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)‖ ≤ Real.sqrt 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.sub_re,
        Complex.one_re]
      have h1s : (1 : ℝ) ≤ ‖1 - s‖ := by
        rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]
        have hh := norm_sub_norm_le s 1
        rw [norm_one] at hh; linarith
      refine (div_le_self (Real.rpow_nonneg (by norm_num) _) h1s).trans ?_
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hC : ‖(-(((2 : ℕ) : ℂ) ^ (-s))) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re,
        show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -s.re ≤ 0)
    rw [hexp]
    refine norm_add₄_le.trans ((add_le_add (add_le_add (add_le_add hA hB) hC)
      (norm_riemannZeta_sub_head_le hs)).trans ?_)
    linarith
theorem norm_riemannXi_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C * (‖s‖ * Real.log ‖s‖)) := by
  obtain ⟨Cγ, hCγ, hγ⟩ := norm_Gamma_le_exp_halfplane
  obtain ⟨Cζ, hCζ, hζ⟩ := norm_riemannZeta_le_const_mul_of_half_le_re
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₀ : ℝ := Cγ / 2 + 3 + (|Real.log Cζ| + Cγ) / (2 * Real.log 2) with hC₀def
  have hfrac : 0 ≤ (|Real.log Cζ| + Cγ) / (2 * Real.log 2) :=
    div_nonneg (add_nonneg (abs_nonneg _) hCγ.le) (by positivity)
  have hC0 : 0 < C₀ := by rw [hC₀def]; linarith [hfrac, hCγ]
  have main : ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C₀ * (‖s‖ * Real.log ‖s‖)) := by
    intro s hs hsnorm
    have hσpos : 0 < s.re := by linarith
    have hN0 : 0 < ‖s‖ := by linarith
    have hL0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hN0
    have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
    have hhalf : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    set P := ‖s‖ * Real.log ‖s‖ with hP
    have hP0 : 0 ≤ P := mul_nonneg hN0.le hL0
    have hPlow : 2 * Real.log 2 ≤ P := by
      rw [hP]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm, hl2, hL0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 2) hL0]
    have hlogP : Real.log ‖s‖ ≤ P := by
      rw [hP]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 1) hL0]
    have hpre : ‖(1 / 2 : ℂ) * (s * (s - 1))‖ ≤ ‖s‖ ^ 2 := by
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      nlinarith [mul_le_mul_of_nonneg_left (by simpa using norm_sub_le s 1) (norm_nonneg s),
        mul_nonneg (norm_nonneg s) (by linarith : (0 : ℝ) ≤ ‖s‖ - 1)]
    have hΓnorm : ‖Gammaℝ s‖ ≤ Real.exp (Cγ * (1 / 2 * P + 1)) := by
      rw [Gammaℝ_def, norm_mul]
      have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
        rw [Complex.div_ofNat_re, Complex.neg_re]; linarith
      have hG : ‖s / 2‖ * Real.log ‖s / 2‖ ≤ 1 / 2 * P := by
        rw [hhalf, hP]
        have hlogle : Real.log (‖s‖ / 2) ≤ Real.log ‖s‖ :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ ‖s‖ / 2 by linarith),
          mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ ‖s‖ / 2)]
      refine (mul_le_mul hπ (hγ (s / 2) (by rw [Complex.div_ofNat_re]; linarith)
        (by rw [hhalf]; linarith)) (norm_nonneg _) (by norm_num)).trans ?_
      exact (one_mul _).trans_le
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hCγ.le))
    have hcombine : ‖riemannXi s‖ ≤ ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖) := by
      rw [riemannXi_eq_prefactor_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hσpos), norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hpre hΓnorm (norm_nonneg _) (by positivity))
        (hζ s hs hsnorm) (norm_nonneg _) (by positivity)
    have hrw : ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖)
        = Real.exp (Real.log Cζ + 3 * Real.log ‖s‖ + Cγ * (1 / 2 * P + 1)) := by
      have hcube : ‖s‖ ^ 3 = Real.exp (3 * Real.log ‖s‖) := by
        rw [← Real.rpow_natCast ‖s‖ 3, Real.rpow_def_of_pos hN0]; congr 1; push_cast; ring
      rw [Real.exp_add, Real.exp_add, Real.exp_log hCζ, ← hcube]; ring
    refine (hcombine.trans_eq hrw).trans (Real.exp_le_exp.mpr ?_)
    have hconst : Real.log Cζ + Cγ ≤ ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * P :=
      calc Real.log Cζ + Cγ ≤ |Real.log Cζ| + Cγ := by linarith [le_abs_self (Real.log Cζ)]
        _ = ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * (2 * Real.log 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hPlow hfrac
    rw [hC₀def]
    linarith [hconst, hlogP]
  refine ⟨4 * C₀, by linarith [hC0], fun s hsnorm ↦ ?_⟩
  by_cases hcase : (1 : ℝ) / 2 ≤ s.re
  · refine (main s hcase hsnorm).trans (Real.exp_le_exp.mpr ?_)
    linarith [mul_nonneg hC0.le (mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖s‖)))]
  · rw [not_le] at hcase
    have hre' : (1 : ℝ) / 2 ≤ (1 - s).re := by simp; linarith
    have hnorm_ge : ‖s‖ ≤ ‖1 - s‖ := by simpa using norm_sub_one_le_norm_of_half_le_re hre'
    have hnorm_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
      have := norm_sub_le (1 : ℂ) s; rw [norm_one] at this; linarith
    have hloga0 : 0 ≤ Real.log ‖1 - s‖ := Real.log_nonneg (by linarith)
    rw [← riemannXi_one_sub s]
    refine (main (1 - s) hre' (hsnorm.trans hnorm_ge)).trans (Real.exp_le_exp.mpr ?_)
    have hloga : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
      have h1 : Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by linarith) hnorm_le
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm]
    have hala : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 4 * (‖s‖ * Real.log ‖s‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hnorm_le hloga0,
        mul_le_mul_of_nonneg_left hloga (by linarith [norm_nonneg s] : (0 : ℝ) ≤ 2 * ‖s‖)]
    linarith [mul_le_mul_of_nonneg_left hala hC0.le]
end
end CertificatePort19
section CertificatePort20
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory Set Function MeromorphicOn Metric
open scoped ENNReal NNReal
private theorem meromorphic_riemannXi : Meromorphic riemannXi :=
  fun z ↦ (analyticOnNhd_riemannXi z (mem_univ z)).meromorphicAt
theorem logCounting_riemannXi_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) R
        ≤ C * (R * Real.log R) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  refine ⟨Cξ + 1 / 2, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  simp only [Set.top_eq_univ]
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      meromorphic_riemannXi hRpos.ne',
    (analyticOnNhd_riemannXi 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero
      (by rw [riemannXi_zero]; norm_num),
    riemannXi_zero,
    show Real.log ‖(1 : ℂ) / 2‖ = -Real.log 2 from by
      rw [Complex.norm_div, norm_one, Complex.norm_ofNat, one_div, Real.log_inv]]
  have hca : Real.circleAverage (fun x ↦ Real.log ‖riemannXi x‖) 0 R ≤ Cξ * (R * Real.log R) := by
    refine Real.circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm (fun z _ ↦ meromorphic_riemannXi z)) fun x hx ↦ ?_
    rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hRpos] at hx
    by_cases hzero : riemannXi x = 0
    · rw [hzero, norm_zero, Real.log_zero]
      exact mul_nonneg hCξ.le (mul_nonneg hRpos.le (Real.log_nonneg (by linarith)))
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero), ← hx]
      exact hξ x (by rw [hx]; exact hR)
  have hl2R : Real.log 2 ≤ 1 / 2 * (R * Real.log R) := by
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR,
      mul_nonneg (show (0 : ℝ) ≤ R - 2 by linarith)
        (Real.log_nonneg (show (1 : ℝ) ≤ R by linarith))]
  linarith
theorem divisor_riemannXi_nonneg : 0 ≤ MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) :=
  analyticOnNhd_riemannXi.divisor_nonneg
theorem divisor_riemannXi_cast_nonneg (z : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast divisor_riemannXi_nonneg z
theorem divisor_riemannXi_toNat_cast (z : ℂ) :
    (((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℕ) : ℝ)
      = ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (divisor_riemannXi_nonneg z)
theorem divisor_riemannXi_apply_zero : MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) 0 = 0 := by
  have hanalytic : AnalyticAt ℂ riemannXi 0 := analyticOnNhd_riemannXi 0 (mem_univ 0)
  change MeromorphicOn.divisor riemannXi univ 0 = 0
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ meromorphic_riemannXi z) (mem_univ 0),
    hanalytic.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannXi_zero]; norm_num))]
  rfl
noncomputable def riemannXiZeroCount (R : ℝ) : ℝ :=
  ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z : ℤ) : ℝ)
theorem divisor_riemannXi_closedBall_eq (R : ℝ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor riemannXi (closedBall 0 R) z = MeromorphicOn.divisor riemannXi ⊤ z := by
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) hz]
  change _ = MeromorphicOn.divisor riemannXi univ z
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) (mem_univ z)]
theorem tsum_toNat_divisor_closedBall (R : ℝ) :
    ∑' z : closedBall (0 : ℂ) R, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
      = ENNReal.ofReal (riemannXiZeroCount R) := by
  have hsupp : (Function.support
      fun w : ℂ ↦ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ)).Finite :=
    ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset fun z hz ↦ by simpa [Function.mem_support] using hz
  have hnn : ∀ w : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ) :=
    fun w ↦ by exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg w
  rw [riemannXiZeroCount, ← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hsupp,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hsupp),
    tsum_subtype (closedBall (0 : ℂ) R)
      (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))]
  refine tsum_congr fun w ↦ ?_
  by_cases hw : w ∈ closedBall (0 : ℂ) R
  · rw [Set.indicator_of_mem hw, divisor_riemannXi_closedBall_eq R hw,
      ← divisor_riemannXi_toNat_cast w, ENNReal.ofReal_natCast]
  · rw [Set.indicator_of_notMem hw,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
    simp
theorem riemannXiZeroCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → riemannXiZeroCount R ≤ C * (R * Real.log R) := by
  obtain ⟨CN, hCN, hN⟩ := logCounting_riemannXi_le
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * CN / Real.log 2, by positivity, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h2Rabs : |2 * R| = 2 * R := abs_of_pos (by linarith)
  have hRHSnn : ∀ z : ℂ, 0 ≤ ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
      (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹) := fun z ↦ by
    by_cases hz2R : z ∈ closedBall (0 : ℂ) (2 * R)
    · rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hznorm : ‖z‖ ≤ 2 * R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz2R
        rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by rwa [h2Rabs])]
        exact mul_nonneg (divisor_riemannXi_cast_nonneg z)
          (Real.log_nonneg (by rw [le_mul_inv_iff₀ hzpos]; linarith))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by rw [h2Rabs]; exact hz2R)]
      simp
  have hkey : Real.log 2 * riemannXiZeroCount R ≤
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R) := by
    rw [show Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R)
          = ∑ᶠ z, ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
              (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹)
            + ((MeromorphicOn.divisor riemannXi ⊤) 0 : ℝ) * Real.log (2 * R) from by
        simp only [Function.locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]]
    rw [divisor_riemannXi_apply_zero, Int.cast_zero, zero_mul, add_zero, riemannXiZeroCount,
      mul_finsum]
    refine finsum_le_finsum' ?_ ?_ ?_
    · refine ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset (fun z hz ↦ ?_)
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hz
      simpa [Function.mem_support] using hz.2
    · refine ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
        (MeromorphicOn.divisor riemannXi ⊤)).finiteSupport
          (isCompact_closedBall 0 |2 * R|)).subset (fun z hz ↦ ?_)
      simpa [Function.mem_support, Int.cast_eq_zero]
        using Function.support_mul_subset_left _ _ hz
    · intro z
      dsimp only
      by_cases hzR : z ∈ closedBall (0 : ℂ) R
      ·
        rw [divisor_riemannXi_closedBall_eq R hzR]
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [divisor_riemannXi_apply_zero]; simp
        · have hznorm : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
          have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by
            rw [h2Rabs]; simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith)]
          have hloglow : Real.log 2 ≤ Real.log (2 * R * ‖z‖⁻¹) :=
            Real.log_le_log (by norm_num) (by rw [le_mul_inv_iff₀ hzpos]; linarith)
          linarith [mul_le_mul_of_nonneg_left hloglow (divisor_riemannXi_cast_nonneg z)]
      ·
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzR, Int.cast_zero, mul_zero]
        exact hRHSnn z
  have hlog2R : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR]
  have hstep : CN * (2 * R * Real.log (2 * R)) ≤ 4 * CN * (R * Real.log R) := by
    rw [show 4 * CN * (R * Real.log R) = CN * (2 * R * (2 * Real.log R)) by ring]
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  linarith [hkey.trans ((hN (2 * R) (by linarith)).trans hstep)]
private theorem exists_dyadic_shell {x : ℝ} (hx : 1 < x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  obtain ⟨n, hn1, hn2⟩ :=
    exists_mem_Ico_zpow (by linarith : (0 : ℝ) < x) (by norm_num : (1 : ℝ) < 2)
  have hn0 : 0 ≤ n := by
    by_contra h
    rw [not_le] at h
    have h1 : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by lia)
    rw [zpow_zero] at h1; linarith
  exact ⟨n.toNat, by rw [← zpow_natCast, Int.toNat_of_nonneg hn0]; exact hn1,
    by rw [← zpow_natCast (2 : ℝ) (n.toNat + 1), Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg hn0]; exact hn2⟩
theorem summable_riemannXiDivisor_norm_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℂ ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) := by
  obtain ⟨Cn, hCn, hn⟩ := riemannXiZeroCount_le
  set g : ℂ → ℝ := fun z ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p) with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z ↦ mul_nonneg (divisor_riemannXi_cast_nonneg z) (by positivity)
  rw [show g = fun z ↦ ((Real.toNNReal (g z) : ℝ≥0) : ℝ) from
      funext fun z ↦ (Real.coe_toNNReal _ (hgnn z)).symm,
    ← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  change (∑' z : ℂ, ENNReal.ofReal (g z)) ≠ ∞
  set s : ℝ := (2 : ℝ) ^ (-p) with hs
  set r : ℝ := 2 * s with hr
  have hreq : r = (2 : ℝ) ^ (1 - p) := by
    rw [hr, hs, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hr0 : 0 < r := by rw [hreq]; positivity
  have hr1 : r < 1 := by
    rw [hreq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A : ℕ → Set ℂ := fun k ↦ {z | (2 : ℝ) ^ k ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (k + 1)}
  have hcover : (univ : Set ℂ) ⊆ closedBall (0 : ℂ) 1 ∪ ⋃ k : ℕ, A k := fun z _ ↦ by
    by_cases h1 : ‖z‖ ≤ 1
    · exact Or.inl (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    · exact Or.inr (mem_iUnion.mpr (exists_dyadic_shell (not_le.mp h1)))
  set B : ℕ → ℝ := fun k ↦ 2 * Cn * Real.log 2 * (((k : ℝ) + 1) * r ^ k) with hB
  have hBnn : ∀ k, 0 ≤ B k := fun k ↦ by rw [hB]; positivity
  have hBsum : Summable B := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0.le])
    rw [hB]
    exact (((h1.add (summable_geometric_of_lt_one hr0.le hr1)).congr
      fun k ↦ by rw [pow_one]; ring).mul_left _)
  have hshell : ∀ k : ℕ, ∑' z : A k, ENNReal.ofReal (g z) ≤ ENNReal.ofReal (B k) := fun k ↦ by
    have h2k1 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      simpa using pow_le_pow_right₀ one_le_two (Nat.le_add_left 1 k)
    have hskeq : ((2 : ℝ) ^ k) ^ (-p) = s ^ k := by
      rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ (-p)) k, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have hlognn : 0 ≤ Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))) :=
      mul_nonneg hCn.le (mul_nonneg (by positivity)
        (Real.log_nonneg (one_le_pow₀ (by norm_num))))
    calc ∑' z : A k, ENNReal.ofReal (g z)
        ≤ ∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
            * ENNReal.ofReal (s ^ k) := by
          refine ENNReal.tsum_le_tsum fun z ↦ ?_
          rw [← ENNReal.ofReal_natCast, divisor_riemannXi_toNat_cast,
            ← ENNReal.ofReal_mul (divisor_riemannXi_cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hg]
          exact mul_le_mul_of_nonneg_left
            (hskeq ▸ Real.rpow_le_rpow_of_nonpos (by positivity) z.2.1 (by linarith))
            (divisor_riemannXi_cast_nonneg _)
      _ = (∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞))
            * ENNReal.ofReal (s ^ k) := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (riemannXiZeroCount (2 ^ (k + 1))) * ENNReal.ofReal (s ^ k) := by
          rw [← tsum_toNat_divisor_closedBall]
          gcongr
          exact ENNReal.tsum_mono_subtype
            (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))
            fun z hz ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2.le
      _ ≤ ENNReal.ofReal (Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))))
            * ENNReal.ofReal (s ^ k) := by gcongr; exact hn _ h2k1
      _ = ENNReal.ofReal (B k) := by
          rw [← ENNReal.ofReal_mul hlognn]
          simp only [hB]
          congr 1
          rw [Real.log_pow, pow_succ, hr, mul_pow]
          push_cast; ring
  have hinner : (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) ≠ ∞ := by
    refine (summable_of_hasFiniteSupport (Set.Finite.subset
      (((MeromorphicOn.divisor riemannXi (closedBall 0 1)).finiteSupport
        (isCompact_closedBall 0 1)).preimage Subtype.coe_injective.injOn)
      fun z hz ↦ ?_)).tsum_ofReal_ne_top
    rw [Set.mem_preimage, Function.mem_support, divisor_riemannXi_closedBall_eq 1 z.2]
    exact fun h0 ↦ hz (by simp only [hg]; rw [h0]; simp)
  have hBtop : (∑' k : ℕ, ENNReal.ofReal (B k)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum]; exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hinner, hBtop⟩) ?_
  calc ∑' z : ℂ, ENNReal.ofReal (g z)
      = ∑' z : (univ : Set ℂ), ENNReal.ofReal (g z) := (tsum_univ _).symm
    _ ≤ ∑' z : (closedBall (0 : ℂ) 1 ∪ (⋃ k : ℕ, A k) : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_mono_subtype (fun w ↦ ENNReal.ofReal (g w)) hcover
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z))
          + ∑' z : (⋃ k : ℕ, A k : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_union_le (fun w ↦ ENNReal.ofReal (g w)) _ _
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) + ∑' k : ℕ, ENNReal.ofReal (B k) := by
        gcongr
        exact (ENNReal.tsum_iUnion_le_tsum (fun w ↦ ENNReal.ofReal (g w)) A).trans
          (ENNReal.tsum_le_tsum hshell)
theorem summable_inv_norm_sq_riemannXiZeros :
    Summable (fun i : (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
        Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat ↦ ‖((i.1 : ℂ))⁻¹‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  refine ((summable_riemannXiDivisor_norm_rpow (show (1 : ℝ) < 2 by norm_num)).subtype
    (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  rw [tsum_fintype]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, divisor_riemannXi_toNat_cast]
  rw [norm_inv, inv_pow, ← Real.rpow_natCast ‖z.1‖ 2, ← Real.rpow_neg (norm_nonneg _)]
  norm_num
end
end CertificatePort20
section CertificatePort21
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeromorphicOn Set Function Metric
abbrev RiemannXiZerosIndex : Type :=
  (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
    Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat
abbrev riemannXiZeros (i : RiemannXiZerosIndex) : ℂ := (i.1 : ℂ)
theorem riemannXiZeros_ne_zero (i : RiemannXiZerosIndex) : riemannXiZeros i ≠ 0 := by
  intro h
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (i.1 : ℂ) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [show (i.1 : ℂ) = 0 from h, divisor_riemannXi_apply_zero] at hmem
  exact hmem rfl
private theorem untop₀_map_natCast (x : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) x).untop₀ = (x.toNat : ℤ) := by
  induction x using ENat.recTopCoe <;> simp
theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ⊤) (z : ℂ) :
    MeromorphicOn.divisor f ⊤ z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ _),
    (hf z (Set.mem_univ _)).meromorphicOrderAt_eq, untop₀_map_natCast]
  rfl
theorem ncard_setOf_riemannXiZeros_eq (z : ℂ) :
    {i | riemannXiZeros i = z}.ncard = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i
      simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset]
    calc {i : RiemannXiZerosIndex |
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)}.ncard
        = Nat.card {i : RiemannXiZerosIndex //
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)} :=
          (Nat.card_coe_set_eq _).symm
      _ = Nat.card (Fin (MeromorphicOn.divisor riemannXi ⊤ z).toNat) :=
          Nat.card_congr (Equiv.sigmaSubtype
            (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support))
      _ = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by simp
  · have hempty : {i | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h
      exact hz (h ▸ i.1.2)
    simp only [Function.mem_support, ne_eq, not_not] at hz
    rw [hempty, Set.ncard_empty, hz, Int.toNat_zero]
theorem divisor_riemannXiCanonicalProduct_riemannXiZeros_eq :
    MeromorphicOn.divisor (riemannXiCanonicalProduct riemannXiZeros) ⊤
      = MeromorphicOn.divisor riemannXi ⊤ := by
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPanalytic : AnalyticOnNhd ℂ (riemannXiCanonicalProduct riemannXiZeros) ⊤ :=
    (differentiable_riemannXiCanonicalProduct riemannXiZeros hsum).differentiableOn.analyticOnNhd
      isOpen_univ
  ext z
  have hξnn : 0 ≤ MeromorphicOn.divisor riemannXi ⊤ z := by
    rw [divisor_eq_analyticOrderNatAt analyticOnNhd_riemannXi z]; positivity
  rw [divisor_eq_analyticOrderNatAt hPanalytic z,
    analyticOrderNatAt_riemannXiCanonicalProduct riemannXiZeros hsum riemannXiZeros_ne_zero z,
    ncard_setOf_riemannXiZeros_eq z, Int.toNat_of_nonneg hξnn]
theorem differentiable_riemannXi_div_canonicalProduct :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ s, g s ≠ 0) ∧
      (∀ s, riemannXi s = g s * riemannXiCanonicalProduct riemannXiZeros s) ∧ g 0 = 1 / 2 := by
  set P := riemannXiCanonicalProduct riemannXiZeros with hP
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPdiff : Differentiable ℂ P := differentiable_riemannXiCanonicalProduct riemannXiZeros hsum
  have hPanalytic : AnalyticOnNhd ℂ P ⊤ := hPdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hξanalytic : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hPmero : MeromorphicOn P ⊤ := hPanalytic.meromorphicOn
  have hξmero : MeromorphicOn riemannXi ⊤ := hξanalytic.meromorphicOn
  have hP0 : P 0 = 1 := riemannXiCanonicalProduct_zero riemannXiZeros
  have hP0ne : P 0 ≠ 0 := by rw [hP0]; norm_num
  set F : ℂ → ℂ := fun s ↦ riemannXi s / P s with hF
  have hFmero : MeromorphicOn F ⊤ := hξmero.div hPmero
  have hmordne : ∀ (f : ℂ → ℂ) (x : ℂ), AnalyticOnNhd ℂ f ⊤ → f x ≠ 0 →
      ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := fun f x hf hx z hz ↦
    meromorphicOrderAt_ne_top_of_isPreconnected hf.meromorphicOn isPreconnected_univ
      (Set.mem_univ x) hz (by
        rw [(hf x (Set.mem_univ _)).meromorphicOrderAt_eq,
          (hf x (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hx]; simp)
  have hξne := hmordne riemannXi 0 hξanalytic (by rw [riemannXi_zero]; norm_num)
  have hPne := hmordne P 0 hPanalytic hP0ne
  have hPinvne : ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt P⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    simpa using hPne z hz
  have hdivF : MeromorphicOn.divisor F ⊤ = 0 := by
    have hFeq : F = riemannXi * P⁻¹ := by
      funext s; simp only [hF, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hFeq, MeromorphicOn.divisor_mul hξmero hPmero.inv hξne hPinvne,
      MeromorphicOn.divisor_inv, hP, divisor_riemannXiCanonicalProduct_riemannXiZeros_eq,
      add_neg_cancel]
  set g := toMeromorphicNFOn F ⊤ with hg
  have hgNF : MeromorphicNFOn g ⊤ := meromorphicNFOn_toMeromorphicNFOn F ⊤
  have hdivg0 : MeromorphicOn.divisor g ⊤ = 0 :=
    (MeromorphicOn.divisor_of_toMeromorphicNFOn hFmero).trans hdivF
  have hganalytic : AnalyticOnNhd ℂ g ⊤ :=
    hgNF.divisor_nonneg_iff_analyticOnNhd.mp (le_of_eq hdivg0.symm)
  have hgdiff : Differentiable ℂ g := fun s ↦ (hganalytic s (Set.mem_univ _)).differentiableAt
  have hFanalytic0 : AnalyticAt ℂ F 0 := by
    rw [hF]; exact (hξanalytic 0 (Set.mem_univ _)).div (hPanalytic 0 (Set.mem_univ _)) hP0ne
  have hF0 : F 0 = 1 / 2 := by
    rw [hF]; change riemannXi 0 / P 0 = 1 / 2; rw [riemannXi_zero, hP0]; norm_num
  have hg0 : g 0 = 1 / 2 := by
    have h1 := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hFmero (Set.mem_univ (0 : ℂ))
    rw [toMeromorphicNFAt_eq_self.mpr hFanalytic0.meromorphicNFAt] at h1
    rw [hg, h1.eq_of_nhds, hF0]
  have hgne : ∀ s, g s ≠ 0 := fun s ↦ by
    rw [← (hgNF (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff]
    have hne : meromorphicOrderAt g s ≠ ⊤ :=
      hmordne g 0 hganalytic (by rw [hg0]; norm_num) s (Set.mem_univ _)
    have hdiv : (meromorphicOrderAt g s).untop₀ = 0 := by
      rw [← MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ s), hdivg0]; rfl
    exact (WithTop.untop₀_eq_zero.mp hdiv).resolve_right hne
  have hFg : F =ᶠ[codiscreteWithin ⊤] g := toMeromorphicNFOn_eqOn_codiscrete hFmero
  have hPneSet : P ⁻¹' {0}ᶜ ∈ codiscreteWithin (⊤ : Set ℂ) :=
    hPanalytic.preimage_zero_mem_codiscreteWithin hP0ne (Set.mem_univ _) isConnected_univ
  have hgPeqξ : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
    have e1 : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] (fun s ↦ F s * P s) :=
      hFg.symm.mul (EventuallyEq.refl _ P)
    have e2 : (fun s ↦ F s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
      filter_upwards [hPneSet] with s hs
      have hsne : P s ≠ 0 := by
        simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      simp only [hF]
      exact div_mul_cancel₀ (riemannXi s) hsne
    exact e1.trans e2
  have hgPanalytic : AnalyticOnNhd ℂ (fun s ↦ g s * P s) ⊤ :=
    fun z hz ↦ (hganalytic z hz).mul (hPanalytic z hz)
  have hle : 𝓝[≠] (0 : ℂ) ≤ codiscreteWithin (⊤ : Set ℂ) := by
    rw [Filter.codiscreteWithin]
    refine le_iSup₂_of_le (0 : ℂ) (Set.mem_univ _) (le_of_eq ?_)
    rw [Set.top_eq_univ, ← Set.compl_eq_univ_sdiff]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun s ↦ g s * P s) z = riemannXi z :=
    (hgPeqξ.filter_mono hle).frequently
  exact ⟨g, hgdiff, hgne, fun s ↦ (hgPanalytic.eqOn_of_preconnected_of_frequently_eq hξanalytic
    isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ s)).symm, hg0⟩
theorem exists_entire_log_riemannXi_div_canonicalProduct :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (1 / 2) ∧
      (∀ s, riemannXi s = Complex.exp (h s) *
        riemannXiCanonicalProduct riemannXiZeros s) := by
  obtain ⟨g, hgdiff, hgne, hgP, hg0⟩ := differentiable_riemannXi_div_canonicalProduct
  set φ : ℂ → ℂ := fun s ↦ deriv g s / g s with hφ
  have hgana : AnalyticOnNhd ℂ g Set.univ := hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hderivdiff : Differentiable ℂ (deriv g) :=
    fun x ↦ (hgana.deriv x (Set.mem_univ _)).differentiableAt
  have hφdiff : Differentiable ℂ φ := hderivdiff.div hgdiff hgne
  obtain ⟨H, hH0, hHderiv⟩ := hφdiff.isExactOn_univ.with_val_at 0 0
  have hHderiv' : ∀ x, HasDerivAt H (φ x) x := fun x ↦ hHderiv x (Set.mem_univ _)
  have hHdiff : Differentiable ℂ H := fun x ↦ (hHderiv' x).differentiableAt
  set k : ℂ → ℂ := fun s ↦ g s * Complex.exp (-H s) with hk
  have hkderiv : ∀ x, HasDerivAt k 0 x := by
    intro x
    have hg_deriv : HasDerivAt g (deriv g x) x := (hgdiff x).hasDerivAt
    have hexp_deriv := ((hHderiv' x).neg).cexp
    have hval : deriv g x * Complex.exp ((-H) x) +
        g x * (Complex.exp ((-H) x) * -φ x) = 0 := by
      simp only [hφ]
      field_simp [hgne x]
      ring
    exact hval ▸ hg_deriv.mul hexp_deriv
  have hkdiff : Differentiable ℂ k := fun x ↦ (hkderiv x).differentiableAt
  have hkconst : ∀ s, k s = k 0 :=
    fun s ↦ is_const_of_deriv_eq_zero hkdiff (fun x ↦ (hkderiv x).deriv) s 0
  have hk0 : k 0 = 1 / 2 := by
    simp only [hk, hH0, neg_zero, Complex.exp_zero, mul_one, hg0]
  refine ⟨fun s ↦ H s + Complex.log (1 / 2), hHdiff.add_const _, by simp [hH0], fun s ↦ ?_⟩
  have hk_eval : g s * Complex.exp (-H s) = 1 / 2 := by
    have := hkconst s; rw [hk0] at this; simpa only [hk] using this
  have hexp : Complex.exp (H s + Complex.log (1 / 2)) = g s := by
    rw [Complex.exp_add, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0), ← hk_eval,
      Complex.exp_neg, mul_comm (g s), ← mul_assoc,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]
  rw [hgP s, hexp]
end
end CertificatePort21
section CertificatePort22
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology MeasureTheory
theorem neg_le_log_norm_weierstrassE1 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    -4 * ‖w‖ ^ 2 ≤ Real.log ‖weierstrassE1 w‖ := by
  set x : ℝ := 2 * ‖w‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 1 / 2 := by rw [hx]; nlinarith [norm_nonneg w]
  have hpos : 0 < 1 - x := by linarith
  have hge : 1 - x ≤ ‖weierstrassE1 w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (weierstrassE1 w)
    rw [norm_one, norm_sub_rev] at h
    linarith [norm_weierstrassE1_sub_one_le hw]
  have hlog : -(2 * x) ≤ Real.log (1 - x) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - x)⁻¹ by positivity)
    rw [Real.log_inv] at h
    nlinarith [mul_inv_cancel₀ hpos.ne', inv_nonneg.mpr hpos.le,
      mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]
  calc -4 * ‖w‖ ^ 2 = -(2 * x) := by rw [hx]; ring
    _ ≤ Real.log (1 - x) := hlog
    _ ≤ Real.log ‖weierstrassE1 w‖ := Real.log_le_log hpos hge
theorem Real.log_add_one_sq_le {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R + 1) ^ 2 ≤ 16 * R ^ (1 / 2 : ℝ) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hnn : 0 ≤ Real.log R + 1 := by linarith [Real.log_nonneg hR]
  have hle : Real.log R + 1 ≤ 4 * R ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hR0 (1 / 4 : ℝ))
    rw [Real.log_rpow hR0] at h; linarith
  calc (Real.log R + 1) ^ 2 ≤ (4 * R ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
    _ = 16 * R ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hR0.le]; norm_num
theorem finite_setOf_riemannXiZeros_eq (z : ℂ) :
    {i : RiemannXiZerosIndex | riemannXiZeros i = z}.Finite := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i : RiemannXiZerosIndex | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i; simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset, ← Set.finite_coe_iff]
    exact Finite.of_equiv _ (Equiv.sigmaSubtype
      (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)).symm
  · have hempty : {i : RiemannXiZerosIndex | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h; exact hz (h ▸ i.1.2)
    rw [hempty]; exact Set.finite_empty
private def zerosInBall (t : ℝ) : Set ℂ :=
  {z | z ∈ (MeromorphicOn.divisor riemannXi ⊤).support ∧ ‖z‖ ≤ t}
private theorem finite_zerosInBall (t : ℝ) : (zerosInBall t).Finite := by
  refine ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t)).finiteSupport
    (isCompact_closedBall 0 t)).subset fun z hz ↦ ?_
  obtain ⟨hzsupp, hzt⟩ := hz
  have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzt
  rw [Function.mem_support, divisor_riemannXi_closedBall_eq t hzb]
  rwa [Function.mem_support] at hzsupp
private theorem setOf_norm_le_eq_biUnion (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}
      = ⋃ z ∈ zerosInBall t, {i : RiemannXiZerosIndex | riemannXiZeros i = z} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  exact ⟨fun hi ↦ ⟨riemannXiZeros i, ⟨i.1.2, hi⟩, rfl⟩, fun ⟨_, ⟨_, hzt⟩, hz⟩ ↦ hz ▸ hzt⟩
theorem finite_setOf_norm_riemannXiZeros_le (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.Finite := by
  rw [setOf_norm_le_eq_biUnion]
  exact (finite_zerosInBall t).biUnion fun z _ ↦ finite_setOf_riemannXiZeros_eq z
theorem ncard_setOf_norm_riemannXiZeros_le_eq (t : ℝ) :
    (({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ)) = riemannXiZeroCount t := by
  have hZfin := finite_zerosInBall t
  set Zf := hZfin.toFinset
  have hncard : {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard
      = ∑ z ∈ Zf, (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
    rw [setOf_norm_le_eq_biUnion,
      Set.Finite.ncard_biUnion hZfin (fun z _ ↦ finite_setOf_riemannXiZeros_eq z) ?_]
    · rw [← hZfin.coe_toFinset, finsum_mem_coe_finset]
      exact Finset.sum_congr rfl fun z _ ↦ ncard_setOf_riemannXiZeros_eq z
    · intro z₁ _ z₂ _ hne
      refine Set.disjoint_left.mpr fun i hi1 hi2 ↦ hne ?_
      simp only [Set.mem_ofPred_eq] at hi1 hi2
      rw [← hi1, ← hi2]
  have hcount : riemannXiZeroCount t
      = ∑ z ∈ Zf, ((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℝ) := by
    have hdef : riemannXiZeroCount t
        = ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z : ℤ) : ℝ) := rfl
    rw [hdef, finsum_eq_finsetSum_of_support_subset _ (s := Zf) ?subset]
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using (hZfin.mem_toFinset.mp hz).2
      rw [divisor_riemannXi_closedBall_eq t hzb]
      exact (divisor_riemannXi_toNat_cast z).symm
    case subset =>
      intro z hz
      have hzint : MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z ≠ 0 :=
        Int.cast_ne_zero.mp (Function.mem_support.mp hz)
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        by_contra hb
        exact hzint (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb)
      rw [Finset.mem_coe, hZfin.mem_toFinset]
      refine ⟨Function.mem_support.mpr ?_, by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzb⟩
      rw [← divisor_riemannXi_closedBall_eq t hzb]; exact hzint
  rw [hncard, hcount, Nat.cast_sum]
theorem exists_card_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      ({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ) ≤ C * (t * Real.log t) := by
  obtain ⟨C, hC, hbound⟩ := riemannXiZeroCount_le
  exact ⟨C, hC, fun t ht ↦ by rw [ncard_setOf_norm_riemannXiZeros_le_eq t]; exact hbound t ht⟩
theorem exists_mem_Icc_forall_le_dist {S : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hcard : 2 * δ * S.card < b - a) :
    ∃ r ∈ Set.Icc a b, ∀ t ∈ S, δ ≤ |r - t| := by
  classical
  set B : Set ℝ := ⋃ t ∈ S, Set.Ioo (t - δ) (t + δ) with hB
  have hlt : volume B < volume (Set.Icc a b) := by
    have hvolB : volume B ≤ ENNReal.ofReal (2 * δ * S.card) := by
      refine (measure_biUnion_finset_le S _).trans ?_
      rw [show ENNReal.ofReal (2 * δ * S.card) = ∑ _t ∈ S, ENNReal.ofReal (2 * δ) from by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring]
      exact Finset.sum_le_sum fun t _ ↦ le_of_eq (by rw [Real.volume_Ioo]; congr 1; ring)
    rw [Real.volume_Icc]
    exact hvolB.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hcard)
  obtain ⟨r, hrIcc, hrB⟩ : (Set.Icc a b \ B).Nonempty :=
    nonempty_of_measure_ne_zero (μ := volume) fun hzero ↦ absurd
      ((measure_mono (Set.subset_sdiff_union (Set.Icc a b) B)).trans
        ((measure_union_le _ _).trans_eq (by rw [hzero, zero_add]))) (not_le.mpr hlt)
  refine ⟨r, hrIcc, fun t ht ↦ ?_⟩
  have hrt : r ∉ Set.Ioo (t - δ) (t + δ) := fun h ↦ hrB (by rw [hB]; exact Set.mem_biUnion ht h)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hrt
  rcases hrt with h | h
  · exact le_abs.mpr (.inr (by linarith))
  · exact le_abs.mpr (.inl (by linarith))
private lemma inv_rpow_mul_rpow {a : ℝ} (ha : 0 < a) (p q : ℝ) :
    a⁻¹ ^ p * a ^ q = a ^ (q - p) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring
theorem summable_inv_norm_rpow_riemannXiZeros {p : ℝ} (hp : 1 < p) :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ p) := by
  rw [summable_sigma_of_nonneg fun _ ↦ by positivity]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  have hbase := summable_riemannXiDivisor_norm_rpow hp
  refine (hbase.subtype (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  have hz0 : z.1 ≠ 0 := by
    intro h
    have hmem := Function.mem_support.mp z.2
    rw [h, divisor_riemannXi_apply_zero] at hmem
    exact hmem rfl
  rw [tsum_fintype]
  simp only [riemannXiZeros, Function.comp_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show ‖z.1⁻¹‖ ^ p = ‖z.1‖ ^ (-p) from by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)],
    divisor_riemannXi_toNat_cast z.1]
private noncomputable def holderSum : ℝ :=
  ∑' i : RiemannXiZerosIndex, ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)
private theorem summable_inv_norm_rpow_three_halves :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :=
  summable_inv_norm_rpow_riemannXiZeros (by norm_num)
private theorem holderSum_nonneg : 0 ≤ holderSum := tsum_nonneg fun _ ↦ by positivity
private theorem tsum_subtype_le_of_le_mul {s : Set RiemannXiZerosIndex}
    {f : RiemannXiZerosIndex → ℝ} (hfs : Summable fun i : s ↦ f (i : RiemannXiZerosIndex))
    {e : ℝ} (he : 0 ≤ e)
    (hf : ∀ i ∈ s, f i ≤ e * ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :
    ∑' i : s, f (i : RiemannXiZerosIndex) ≤ (holderSum + 1) * e :=
  calc ∑' i : s, f (i : RiemannXiZerosIndex)
      ≤ ∑' i : s, e * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) :=
        Summable.tsum_le_tsum (fun i ↦ hf i i.2) hfs
          ((summable_inv_norm_rpow_three_halves.subtype s).mul_left _)
    _ = e * ∑' i : s, ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ e * holderSum :=
        mul_le_mul_of_nonneg_left
          (summable_inv_norm_rpow_three_halves.tsum_subtype_le _ s fun _ ↦ by positivity) he
    _ ≤ (holderSum + 1) * e := by nlinarith [holderSum_nonneg]
theorem exists_sum_inv_norm_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le t).toFinset, ‖(riemannXiZeros i)⁻¹‖
        ≤ C * t ^ (1 / 2 : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  rw [← Finset.tsum_subtype (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)]
  refine tsum_subtype_le_of_le_mul (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)
    (e := t ^ (1 / 2 : ℝ)) Summable.of_finite (Real.rpow_nonneg ht _) fun i hi ↦ ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  calc a⁻¹
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (1 / 2 - 3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hi (by norm_num)) (by positivity)
    _ = t ^ (1 / 2 : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
theorem exists_sum_inv_norm_sq_riemannXiZeros_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      ∑' i : {i : RiemannXiZerosIndex // t < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 ≤ C * t ^ (-(1 / 2) : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  refine tsum_subtype_le_of_le_mul (s := {i | t < ‖riemannXiZeros i‖})
    (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) (e := t ^ (-(1 / 2) : ℝ))
    (summable_inv_norm_sq_riemannXiZeros.subtype _) (Real.rpow_nonneg ht.le _) fun i hi ↦ ?_
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := lt_trans ht hi
  calc a⁻¹ ^ 2
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (-(1 / 2) - 3 / 2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) by norm_num,
          Real.rpow_mul ha.le, Real.rpow_natCast, Real.rpow_neg_one, ← inv_pow]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ht hi.le (by norm_num)) (by positivity)
    _ = t ^ (-(1 / 2) : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
private lemma self_mul_rpow_half {R : ℝ} (hR : 0 < R) :
    R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]
private lemma far_rpow_id {R : ℝ} (hR : 0 < R) :
    16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ) = 8 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; norm_num
  have hRid : R ^ 2 * R ^ (-(1 / 2) : ℝ) = R ^ (3 / 2 : ℝ) := by
    have h2 : R ^ 2 = R ^ (2 : ℝ) := by rw [← Real.rpow_natCast R 2]; norm_num
    rw [h2, ← Real.rpow_add hR, show (2 : ℝ) + -(1 / 2) = 3 / 2 by norm_num]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 16 * R ^ 2 * (1 / 2 * R ^ (-(1 / 2) : ℝ)) = 8 * (R ^ 2 * R ^ (-(1 / 2) : ℝ)) by ring, hRid]
private lemma near_rpow_id {R : ℝ} (hR : 0 < R) :
    2 * R * (4 * R) ^ (1 / 2 : ℝ) = 4 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 2 * R * (2 * R ^ (1 / 2 : ℝ)) = 4 * (R * R ^ (1 / 2 : ℝ)) by ring, self_mul_rpow_half hR]
theorem exists_tsum_far_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ 2 * R →
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
  obtain ⟨C2, hC2pos, hC2⟩ := exists_sum_inv_norm_sq_riemannXiZeros_tail_le
  refine ⟨8 * C2, by positivity, fun R hR s hs ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hsublog := (summable_log_norm_weierstrassE1 riemannXiZeros
    summable_inv_norm_sq_riemannXiZeros s).subtype {i | 4 * R < ‖riemannXiZeros i‖}
  have hsubinv := (summable_inv_norm_sq_riemannXiZeros.subtype
    {i | 4 * R < ‖riemannXiZeros i‖}).mul_left (-16 * R ^ 2)
  have hterm : ∀ i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
      -16 * R ^ 2 * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2
        ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
    intro i
    set ρ := riemannXiZeros (i : RiemannXiZerosIndex) with hρ
    have hρpos : (0 : ℝ) < ‖ρ‖ := lt_trans h4R i.2
    refine le_trans ?_ (neg_le_log_norm_weierstrassE1
      (show ‖s / ρ‖ ≤ 1 / 2 by rw [norm_div, div_le_iff₀ hρpos]; linarith [i.2]))
    rw [show ‖s / ρ‖ ^ 2 = ‖s‖ ^ 2 * ‖ρ⁻¹‖ ^ 2 by rw [norm_div, norm_inv]; ring]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * R ^ 2 - 4 * ‖s‖ ^ 2 by
      nlinarith [hs, norm_nonneg s, hRpos]) (sq_nonneg ‖ρ⁻¹‖)]
  refine le_trans ?_
    (Summable.tsum_le_tsum (L := SummationFilter.unconditional _) hterm hsubinv hsublog)
  rw [tsum_mul_left]
  calc -(8 * C2 * R ^ (3 / 2 : ℝ))
      = -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ)) := by
        rw [show -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ))
          = -(C2 * (16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ))) by ring, far_rpow_id hRpos]; ring
    _ ≤ -16 * R ^ 2 * ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonpos_left (hC2 (4 * R) h4R) (by nlinarith [sq_nonneg R, hRpos])
theorem exists_finset_near_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (∀ i : RiemannXiZerosIndex, ‖riemannXiZeros i‖ ≤ 4 * R → s ≠ riemannXiZeros i) ∧
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset,
          Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
  obtain ⟨Cn, hCnpos, hCn⟩ := exists_card_riemannXiZeros_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_inv_norm_riemannXiZeros_le
  set Clog : ℝ := Real.log (256 * Cn + 4) + 2 with hClog
  have hlogc : (0 : ℝ) ≤ Real.log (256 * Cn + 4) := Real.log_nonneg (by linarith)
  have hcc : (0 : ℝ) ≤ 12 * Cn * Clog := by rw [hClog]; nlinarith
  refine ⟨4 * C1 + 192 * Cn * Clog, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  set m := F.card with hm
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set δ : ℝ := R / (4 * ((m : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := div_pos hRpos (by positivity)
  have hδid : δ * (4 * ((m : ℝ) + 1)) = R := by rw [hδ]; field_simp
  have hmcard : (m : ℝ) ≤ Cn * (4 * R * Real.log (4 * R)) := by
    rw [hm, hF, ← Set.ncard_eq_toFinset_card _ (finite_setOf_norm_riemannXiZeros_le (4 * R))]
    exact hCn (4 * R) (by linarith)
  obtain ⟨R', hR'mem, hR'dist⟩ :=
    exists_mem_Icc_forall_le_dist (S := F.image fun i ↦ ‖riemannXiZeros i‖) (a := R) (b := 2 * R)
      hδpos (by
        have hci : ((F.image fun i ↦ ‖riemannXiZeros i‖).card : ℝ) ≤ (m : ℝ) := by
          rw [hm]; exact_mod_cast Finset.card_image_le
        nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hci), mul_nonneg hδpos.le hmnn])
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  have hR'le : R' ≤ 2 * R := hR'mem.2
  have hdist : ∀ i ∈ F, δ ≤ ‖s - riemannXiZeros i‖ := fun i hiF ↦
    (hR'dist _ (Finset.mem_image_of_mem _ hiF)).trans <| by
      simpa only [hs] using abs_norm_sub_norm_le s (riemannXiZeros i)
  have hne : ∀ i ∈ F, s ≠ riemannXiZeros i := fun i hiF heq ↦ by
    have hd := hdist i hiF; rw [heq, sub_self, norm_zero] at hd; linarith
  refine ⟨fun i hi ↦ hne i (by rw [hF, Set.Finite.mem_toFinset]; exact hi), ?_⟩
  have hlogd : Real.log δ - Real.log (4 * R) = -Real.log (16 * ((m : ℝ) + 1)) := by
    rw [← Real.log_div hδpos.ne' (by positivity), ← Real.log_inv]
    congr 1
    rw [hδ]; field_simp; ring
  have hpt : ∀ i ∈ F, Real.log δ - Real.log (4 * R) - 2 * R * ‖(riemannXiZeros i)⁻¹‖
      ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
    intro i hiF
    set ρ := riemannXiZeros i with hρ
    have hρne : ρ ≠ 0 := riemannXiZeros_ne_zero i
    have hi4R : ‖ρ‖ ≤ 4 * R := by have h := hiF; rw [hF, Set.Finite.mem_toFinset] at h; exact h
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
    have hsne : s ≠ ρ := hne i hiF
    rw [log_norm_weierstrassE1 (fun h ↦ hsne ((div_eq_one_iff_eq hρne).mp h)),
      show ‖(1 : ℂ) - s / ρ‖ = ‖s - ρ‖ / ‖ρ‖ by
        rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ by rw [sub_div, div_self hρne], norm_div,
          norm_sub_rev],
      Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsne)) hρpos.ne']
    have hb2 : ‖s / ρ‖ ≤ 2 * R * ‖ρ⁻¹‖ := by
      rw [norm_div, norm_inv, hs, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hR'le (by positivity)
    linarith [Real.log_le_log hδpos (hdist i hiF), Real.log_le_log hρpos hi4R,
      (abs_le.mp (Complex.abs_re_le_norm (s / ρ))).1]
  refine le_trans ?_ (Finset.sum_le_sum hpt)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hlogd, mul_neg]
  have h2Rsum : 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖ ≤ 4 * C1 * R ^ (3 / 2 : ℝ) :=
    calc 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖
        ≤ 2 * R * (C1 * (4 * R) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [hF]; exact hC1 (4 * R) (by linarith)) (by linarith)
      _ = C1 * (2 * R * (4 * R) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * C1 * R ^ (3 / 2 : ℝ) := by rw [near_rpow_id hRpos]; ring
  have hmlog : (m : ℝ) * Real.log (16 * ((m : ℝ) + 1)) ≤ 192 * Cn * Clog * R ^ (3 / 2 : ℝ) := by
    have hCn4R : (0 : ℝ) ≤ Cn * (4 * R) := by positivity
    have hm12 : (m : ℝ) ≤ 12 * Cn * R * (Real.log R + 1) := by
      have h : Real.log (4 * R) ≤ 3 * (Real.log R + 1) := by
        rw [Real.log_mul (by norm_num) hRpos.ne']
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hm16 : (m : ℝ) ≤ 16 * Cn * R ^ 2 := by
      have h : Real.log (4 * R) ≤ 4 * R :=
        by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * R by linarith)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hlogm : Real.log (16 * ((m : ℝ) + 1)) ≤ Clog * (Real.log R + 1) := by
      have hmono := Real.log_le_log (show (0 : ℝ) < 16 * ((m : ℝ) + 1) by positivity)
        (show 16 * ((m : ℝ) + 1) ≤ (256 * Cn + 4) * R ^ 2 by nlinarith [hm16])
      rw [Real.log_mul (by positivity) (by positivity : (R : ℝ) ^ 2 ≠ 0), Real.log_pow] at hmono
      rw [hClog]
      push_cast at hmono ⊢
      nlinarith [mul_nonneg hlogc hlogR]
    have hRL2 : R * (Real.log R + 1) ^ 2 ≤ 16 * R ^ (3 / 2 : ℝ) := by
      rw [← self_mul_rpow_half hRpos]
      nlinarith [Real.log_add_one_sq_le hR1, hRpos]
    have hstep := mul_le_mul hm12 hlogm (Real.log_nonneg (by linarith))
      (by positivity : (0 : ℝ) ≤ 12 * Cn * R * (Real.log R + 1))
    nlinarith [mul_le_mul_of_nonneg_left hRL2 hcc]
  linarith only [hmlog, h2Rsum]
theorem exists_circle_log_norm_riemannXiCanonicalProduct_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      riemannXiCanonicalProduct riemannXiZeros s ≠ 0 ∧
        -(C * R ^ (3 / 2 : ℝ)) ≤ Real.log ‖riemannXiCanonicalProduct riemannXiZeros s‖ := by
  obtain ⟨CF, hCFpos, hCF⟩ := exists_tsum_far_log_norm_weierstrassE1_ge
  obtain ⟨CN, hCNpos, hCN⟩ := exists_finset_near_log_norm_weierstrassE1_ge
  refine ⟨CF + CN, by linarith, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hCN R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hne_near, hnear⟩ := hR' s hs
  have hs2R : ‖s‖ ≤ 2 * R := by rw [hs]; exact hR'mem.2
  have hsum := summable_inv_norm_sq_riemannXiZeros
  have hsumlog := summable_log_norm_weierstrassE1 riemannXiZeros hsum s
  have hsne : ∀ i, s ≠ riemannXiZeros i := by
    intro i
    rcases le_or_gt ‖riemannXiZeros i‖ (4 * R) with hle | hlt
    · exact hne_near i hle
    · intro heq
      rw [← heq, hs] at hlt
      linarith [hR'mem.2]
  refine ⟨riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros hsum hsne, ?_⟩
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  have hfar : -(CF * R ^ (3 / 2 : ℝ))
      ≤ ∑' x : ↥((↑F : Set RiemannXiZerosIndex)ᶜ),
          Real.log ‖weierstrassE1 (s / riemannXiZeros (x : RiemannXiZerosIndex))‖ := by
    rw [show ((↑F : Set RiemannXiZerosIndex)ᶜ) = {i | 4 * R < ‖riemannXiZeros i‖} by
      rw [hF, Set.Finite.coe_toFinset]
      ext i; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
    exact hCF R hR s hs2R
  rw [log_norm_riemannXiCanonicalProduct riemannXiZeros hsum hsne,
    ← hsumlog.sum_add_tsum_compl (s := F)]
  linarith [hnear, hfar]
end
end CertificatePort22
section CertificatePort23
/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
-/
section
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ f z / z) 0 (deriv f 0)
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ)
    (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  apply Function.update_of_ne z_ne_0
lemma AnalyticOn_divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) :
    AnalyticOn ℂ (divRemovable_zero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0]
  constructor
  · have (x) (hx : x ∈ s \ {0}) : x ≠ 0 := by
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      exact hx.right
    rw [differentiableOn_congr (fun x hyp_x => Function.update_of_ne (this x hyp_x) _ _)]
    exact
      (analytic.mono Set.sdiff_subset).differentiableOn.fun_div
      (differentiableOn_id.mono (Set.subset_univ (s \ {0})))
      this
  · have U :=
      HasDerivAt.continuousAt_div (c := 0) (a := deriv f 0)
        (f := f)
        (DifferentiableOn.hasDerivAt
          ((Complex.analyticOn_iff_differentiableOn o).mp analytic)
          sInNhds0)
    simpa [divRemovable_zero, zero] using U
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ}
    {R : ℝ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) :
    AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  simp only [Metric.mem_closedBall, dist_zero_right] at x_hyp
  cases x_hyp.eq_or_lt with
  | inl h =>
    use Metric.ball x (R / 2)
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp [Rpos]
    · have (x₂) (hyp_x₂ : x₂ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2)) : x₂ ≠ 0 := by
        rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
          Set.mem_ofPred_eq] at hyp_x₂
        rw [← norm_pos_iff]
        calc 0
          _ < R - ‖x₂ - x‖ := by
            obtain ⟨-, v⟩ := hyp_x₂
            linarith
          _ = ‖x‖ - ‖x - x₂‖ := by
            rw [h, norm_sub_rev]
          _ ≤ ‖x - (x - x₂)‖ := norm_sub_norm_le ..
          _ ≤ ‖x₂‖ := by rw [sub_sub_cancel]
      apply AnalyticOn.congr
      · exact (analytic.mono Set.inter_subset_left).div analyticOn_id this
      · intro x₃ hyp_x₃
        exact divRemovable_zero_of_ne_zero _ (this _ hyp_x₃)
  | inr h =>
    use Metric.ball 0 R
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp only [ball_eq, sub_zero, Set.mem_ofPred_eq, h]
    · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R =
        Metric.ball (0 : ℂ) R := by
        apply Set.inter_eq_self_of_subset_right
        exact Metric.ball_subset_closedBall
      rw [si]
      exact AnalyticOn_divRemovable_zero
        (Metric.ball_mem_nhds 0 Rpos)
        zero Metric.isOpen_ball
        (analytic.mono Metric.ball_subset_closedBall)
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) :
    ℂ → ℂ :=
  fun z ↦ divRemovable_zero f z / (2 * M - f z)
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ}
    (M : ℝ) (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) :
    AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) :=
  AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos analytic zero)
    (AnalyticOn.sub analyticOn_const analytic) nonzero
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ}
    {x : ℂ} (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) :
    ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  rw [calc
    (2 * M - x).re * (2 * M - x).re +
        (2 * M - x).im * (2 * M - x).im =
      (2 * M - x.re) * (2 * M - x.re) +
        x.im * x.im := by simp
    _ = x.re * x.re +
        (x.im * x.im + 4 * M * (M - x.re)) := by ring]
  bound
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ}
    {f : ℂ → ℂ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have zInSFunc :
      ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    exact Set.mem_of_mem_of_subset hyp_z <|
      (Metric.sphere_subset_closedBall).trans
        (Metric.closedBall_subset_closedBall hyp_r)
  have fPosAll :
      ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, sub_pos]
      linarith [realPartBounded z zInS])
  have schwartzQuotientBounded :
      ∀ z ∈ Metric.sphere 0 R,
      ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc R le_rfl z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z
    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by
        simp only [Complex.norm_div, divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left
            (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le
              Mpos (realPartBounded z zInS))
      _ ≤ 1 / ‖z‖ := by
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (div_self_le_one _) (norm_nonneg _)
      _ = 1 / R := by rw [hyp_z]
  have maxMod (z) (hz : z ∈ Metric.closedBall 0 R) : ‖schwartzQuotient f M z‖ ≤ 1 / R :=
    AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      schwartzQuotientBounded hz
  have boundForF :
      ∀ r < R, 0 < r →
      ∀ z ∈ Metric.sphere 0 r,
      ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc r hyp_r.le z zOnR
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by
      rwa [← norm_pos_iff, zOnR]
    simp only [divRemovable_zero_of_ne_zero f U, Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by
      simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq, fPosAll z zInS,
        not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 :
        ‖f z‖ ≤ 2 * M * r / R + (r / R) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          grw [norm_sub_le]
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          simp [Mpos.le]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by
          ring_nf
    rw [← tsub_le_iff_right, ← one_sub_mul, ← le_div_iff₀'] at U0
    · have hR : (R : ℝ) ≠ 0 := Rpos.ne'
      have hRr : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyp_r).symm
      have heq : 2 * M * r / (R - r) = 2 * M * r / R / (1 - r / R) := by
        rw [one_sub_div hR]; field_simp
      rw [heq]
      exact U0
    · rwa [sub_pos, div_lt_one₀ Rpos]
  have maxBoundForF
      (r) (hyp_r : r < R) (pos_r : 0 < r)
      (z) (hz : z ∈ Metric.closedBall 0 r) :
      ‖f z‖ ≤ 2 * M * r / (R - r) :=
    AnalyticOn.norm_le_of_norm_le_on_sphere hyp_r.le analytic (boundForF r hyp_r pos_r) hz
  have U : 0 ≤ r := by
    rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
    exact (norm_nonneg z).trans hyp_z
  cases U.eq_or_lt' with
  | inl pos_r =>
    obtain rfl : z = 0 := by
      rwa [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z
    rwa [pos_r, mul_zero, sub_zero, zero_div, norm_le_zero_iff]
  | inr pos_r =>
    exact maxBoundForF r hyp_r pos_r z hyp_z
end
end CertificatePort23
section CertificatePort24
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Set Metric
theorem re_log_riemannXi_div_canonicalProduct_le {h : ℂ → ℂ}
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (h s).re ≤ C * R ^ (3 / 2 : ℝ) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  obtain ⟨CP, hCP, hP⟩ := exists_circle_log_norm_riemannXiCanonicalProduct_ge
  refine ⟨Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP, by positivity, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hP R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hPne, hlogP⟩ := hR' s hs
  set P := riemannXiCanonicalProduct riemannXiZeros
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hs ▸ hR.trans hR'mem.1
  have hPpos : 0 < ‖P s‖ := norm_pos_iff.mpr hPne
  have hnormξ : ‖riemannXi s‖ = Real.exp ((h s).re) * ‖P s‖ := by
    rw [hrep s, norm_mul, Complex.norm_exp]
  have hξpos : 0 < ‖riemannXi s‖ := by rw [hnormξ]; positivity
  have hre_eq : (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := by
    rw [hnormξ, Real.log_mul (Real.exp_pos _).ne' hPpos.ne', Real.log_exp, add_sub_cancel_right]
  have hlogξ : Real.log ‖riemannXi s‖ ≤ Cξ * (‖s‖ * Real.log ‖s‖) :=
    (Real.log_le_iff_le_exp hξpos).2 (hξ s hs2)
  have hsl : ‖s‖ * Real.log ‖s‖ ≤ 2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hR0]
    have hlog : Real.log ‖s‖ ≤ 2 * ‖s‖ ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (norm_nonneg s) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hmul : ‖s‖ * ‖s‖ ^ (1 / 2 : ℝ) = ‖s‖ ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have hpow : ‖s‖ ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg s) (hs ▸ hR'mem.2) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hlog (norm_nonneg s)]
  calc (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := hre_eq
    _ ≤ Cξ * (‖s‖ * Real.log ‖s‖) + CP * R ^ (3 / 2 : ℝ) := by linarith
    _ ≤ Cξ * (2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ))) + CP * R ^ (3 / 2 : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hsl hCξ.le]
    _ = (Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP) * R ^ (3 / 2 : ℝ) := by ring
end
end CertificatePort24
section CertificatePort25
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Set Metric
theorem exists_affine_log_riemannXi_div_canonicalProduct {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ A B : ℂ, ∀ s, h s = A + B * s := by
  obtain ⟨C, hCpos, hgrow⟩ := re_log_riemannXi_div_canonicalProduct_le hrep
  have hderivdiff : Differentiable ℂ (deriv h) := fun x ↦
    ((analyticOnNhd_univ_iff_differentiable.mpr hdiff).deriv x (mem_univ x)).differentiableAt
  set C₀ : ℝ := 2 * C + 3 * ‖h 0‖ + 2 with hC₀def
  have claimA : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖h z‖ ≤ C₀ * R ^ (3 / 2 : ℝ) := by
    intro R hR z hz
    obtain ⟨R', hR'mem, hR'⟩ := hgrow R hR
    have hR'pos : 0 < R' := by linarith [hR'mem.1]
    have hRpow1 : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCR : 0 ≤ C * R ^ (3 / 2 : ℝ) :=
      mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _)
    have hmax : ∀ w : ℂ, ‖w‖ ≤ R' → (h w).re ≤ C * R ^ (3 / 2 : ℝ) := by
      intro w hw
      have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) R'),
          ‖Complex.exp (h ζ)‖ ≤ Real.exp (C * R ^ (3 / 2 : ℝ)) := fun ζ hζ ↦ by
        rw [frontier_ball 0 hR'pos.ne'] at hζ
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hR' ζ (by simpa using mem_sphere_iff_norm.mp hζ))
      have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        hdiff.cexp.diffContOnCl hfront
        (by rw [closure_ball 0 hR'pos.ne']; simpa [mem_closedBall, dist_eq_norm] using hw)
      rw [Complex.norm_exp] at hle
      exact Real.exp_le_exp.mp hle
    have hbc := borelCaratheodory_closedBall (f := fun s ↦ h s - h 0) (z := z) (r := R' / 2)
      (M := C * R ^ (3 / 2 : ℝ) + ‖h 0‖ + 1) hR'pos
      ((analyticOn_univ_iff_differentiable.mpr (hdiff.sub_const (h 0))).mono (subset_univ _))
      (by simp) (by linarith [norm_nonneg (h 0)])
      (fun ζ hζ ↦ by
        rw [mem_closedBall, dist_eq_norm, sub_zero] at hζ
        simp only [Complex.sub_re]
        linarith [hmax ζ hζ, (neg_le_abs (h 0).re).trans (abs_re_le_norm (h 0))])
      (by linarith) (by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith [hR'mem.1])
    rw [show R' - R' / 2 = R' / 2 by ring, mul_div_assoc, div_self (half_pos hR'pos).ne',
      mul_one] at hbc
    rw [hC₀def]
    nlinarith [hbc, norm_sub_norm_le (h z) (h 0), norm_nonneg (h 0),
      mul_nonneg (norm_nonneg (h 0)) (sub_nonneg.mpr hRpow1)]
  have claimB : ∀ c : ℂ, iteratedDeriv 2 h c = 0 := by
    intro c
    have htend : Tendsto (fun R : ℝ ↦ 32 * C₀ * R ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (32 * C₀)
    refine norm_le_zero_iff.mp <| ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop (4 * ‖c‖ + 2)] with R hR
    have hR2 : 2 ≤ R := by linarith [norm_nonneg c]
    have hRpos : 0 < R := by linarith
    set ρ : ℝ := R / 2 - ‖c‖ with hρdef
    have hρ4 : R / 4 ≤ ρ := by rw [hρdef]; linarith
    have hρpos : 0 < ρ := by linarith
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρpos
      hdiff.diffContOnCl (fun z hz ↦ claimA R hR2 z (by
        have hzc := norm_sub_norm_le z c
        rw [mem_sphere_iff_norm.mp hz, hρdef] at hzc
        linarith))
    rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]] at hcauchy
    have hpowid : R ^ (3 / 2 : ℝ) / R ^ 2 = R ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_sub hRpos]; norm_num
    calc ‖iteratedDeriv 2 h c‖ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / ρ ^ 2 := hcauchy
      _ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / (R ^ 2 / 16) := by
          gcongr; nlinarith [hρ4, hρpos]
      _ = 32 * C₀ * (R ^ (3 / 2 : ℝ) / R ^ 2) := by ring
      _ = 32 * C₀ * R ^ (-(1 / 2) : ℝ) := by rw [hpowid]
  have hderivconst : ∀ x : ℂ, deriv h x = deriv h 0 := fun x ↦
    is_const_of_deriv_eq_zero hderivdiff
      (fun y ↦ by simpa [iteratedDeriv_succ, iteratedDeriv_one] using claimB y) x 0
  refine ⟨h 0, deriv h 0, fun s ↦ ?_⟩
  have key : h s - deriv h 0 * s = h 0 := by
    simpa using is_const_of_deriv_eq_zero (f := fun y : ℂ ↦ h y - deriv h 0 * y)
      (hdiff.sub (differentiable_id.const_mul _))
      (fun x ↦ by
        have hd : HasDerivAt (fun y : ℂ ↦ h y - deriv h 0 * y) (deriv h x - deriv h 0) x :=
          (hdiff x).hasDerivAt.sub (by simpa using (hasDerivAt_id x).const_mul (deriv h 0))
        rw [hd.deriv, hderivconst x]; ring) s 0
  linear_combination key
end
end CertificatePort25
section CertificatePort26
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Set
open scoped ComplexConjugate
theorem logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) 0 = 0 := by
  set ρ := riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i) with hf
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hf0 : ∀ i, f i 0 = 1 := fun i ↦ by simp [hf]
  have hlog0 : ∀ i, logDeriv (f i) 0 = 0 := fun i ↦ by
    have hu : HasDerivAt (fun s : ℂ ↦ s / ρ i) (ρ i)⁻¹ 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℂ)).div_const (ρ i)
    have hde : HasDerivAt (f i) 0 0 := by
      simpa [hf, Function.comp_def] using (hasDerivAt_weierstrassE1 ((0 : ℂ) / ρ i)).comp 0 hu
    rw [logDeriv_apply, hde.deriv, hf0 i, zero_div]
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ (0 : ℂ))
    (fun i ↦ by rw [hf0 i]; norm_num) hd (by simp only [hlog0]; exact summable_zero)
    ((hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ
      summable_inv_norm_sq_riemannXiZeros).multipliableLocallyUniformlyOn)
    (by simp only [hf0, tprod_one]; norm_num)
  simp only [hlog0, tsum_zero] at hkey
  exact hkey
theorem logDeriv_riemannXi_zero_eq_deriv {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = deriv h 0 := by
  have hP0ne : riemannXiCanonicalProduct riemannXiZeros 0 ≠ 0 := by
    rw [riemannXiCanonicalProduct_zero]; norm_num
  rw [funext hrep, logDeriv_mul (f := fun s ↦ Complex.exp (h s))
      (g := riemannXiCanonicalProduct riemannXiZeros) 0 (Complex.exp_ne_zero _) hP0ne
      (hdiff 0).hasDerivAt.cexp.differentiableAt
      (differentiable_riemannXiCanonicalProduct riemannXiZeros
        summable_inv_norm_sq_riemannXiZeros 0),
    show (fun s ↦ Complex.exp (h s)) = Complex.exp ∘ h from rfl,
    logDeriv_comp (Complex.differentiable_exp (h 0)) (hdiff 0), Complex.logDeriv_exp,
    logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero]
  simp
theorem log_riemannXi_div_canonicalProduct_const_eq {h : ℂ → ℂ} {A B : ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s)
    (haffine : ∀ s, h s = A + B * s) :
    Complex.exp A = 1 / 2 ∧ B = logDeriv riemannXi 0 ∧ conj B = B := by
  have hexpA : Complex.exp A = 1 / 2 := by
    have h0 := hrep 0
    rw [riemannXi_zero, riemannXiCanonicalProduct_zero, mul_one, haffine 0, mul_zero,
      add_zero] at h0
    exact h0.symm
  have hBeq : B = logDeriv riemannXi 0 := by
    rw [logDeriv_riemannXi_zero_eq_deriv hdiff hrep, funext haffine]; simp
  have hsym : conj ∘ riemannXi ∘ conj = riemannXi := by
    funext s; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have hreal : conj (deriv riemannXi 0) = deriv riemannXi 0 := by
    simpa using congrFun (by rw [← deriv_conj_conj, hsym] :
      conj ∘ deriv riemannXi ∘ conj = deriv riemannXi) 0
  refine ⟨hexpA, hBeq, ?_⟩
  rw [hBeq, logDeriv_apply, map_div₀, hreal, riemannXi_zero, map_div₀, map_one, map_ofNat]
theorem riemannXi_eq_hadamard_product :
    ∃ B : ℝ, ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s := by
  obtain ⟨h, hdiff, _, hrep⟩ := exists_entire_log_riemannXi_div_canonicalProduct
  obtain ⟨A, B, haffine⟩ := exists_affine_log_riemannXi_div_canonicalProduct hdiff hrep
  obtain ⟨hexpA, _, hBreal⟩ := log_riemannXi_div_canonicalProduct_const_eq hdiff hrep haffine
  refine ⟨B.re, fun s ↦ ?_⟩
  have hBre : (B.re : ℂ) = B := Complex.conj_eq_iff_re.mp hBreal
  rw [hrep s, haffine s, Complex.exp_add, hexpA, hBre]
end
end CertificatePort26
section CertificatePort27
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Set
open scoped Real
private lemma logDeriv_weierstrassE1_div {ρ : ℂ} (hρ : ρ ≠ 0) {s : ℂ} (hs : s ≠ ρ) :
    logDeriv (fun z ↦ weierstrassE1 (z / ρ)) s = 1 / (s - ρ) + 1 / ρ := by
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : s / ρ ≠ 1 := fun h ↦ hs ((div_eq_one_iff_eq hρ).mp h)
  have h1ρ : (1 : ℂ) - s / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hu : HasDerivAt (fun z : ℂ ↦ z / ρ) (1 / ρ) s := by
    simpa using (hasDerivAt_id s).div_const ρ
  have hc : HasDerivAt (fun z ↦ weierstrassE1 (z / ρ))
      (-(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)) s := by
    have h := (hasDerivAt_weierstrassE1 (s / ρ)).comp s hu
    simpa [Function.comp_def] using h
  rw [logDeriv_apply, hc.deriv]
  simp only [weierstrassE1]
  rw [show -(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)
        = (-(s / ρ) * (1 / ρ)) * Complex.exp (s / ρ) by ring,
      mul_div_mul_right _ _ (Complex.exp_ne_zero _), div_eq_iff h1ρ]
  field_simp
  ring
theorem summable_partial_fraction {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ 1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  have hu : Summable (fun i ↦ 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * (‖s‖ + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (‖s‖ + 1))) ^ 2 := by positivity
    filter_upwards [hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [htail] with i hi
  have hρpos : 0 < ‖ρ i‖ := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  have hsρpos : 0 < ‖s - ρ i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs i))
  have hbig : 2 * (‖s‖ + 1) ≤ ‖ρ i‖ := by
    rw [norm_inv, one_div] at hi
    exact (inv_le_inv₀ hρpos (by positivity)).mp hi
  have hge : ‖ρ i‖ / 2 ≤ ‖s - ρ i‖ := by
    have h1 : ‖ρ i‖ - ‖s‖ ≤ ‖s - ρ i‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    nlinarith [norm_nonneg s]
  have hinv : ‖(s - ρ i)⁻¹‖ ≤ 2 * ‖(ρ i)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    rw [show 2 * ‖ρ i‖⁻¹ = (‖ρ i‖ / 2)⁻¹ by rw [inv_div]; ring]
    exact inv_anti₀ (by positivity) hge
  have hρi : ρ i ≠ 0 := riemannXiZeros_ne_zero i
  have hsρi : s - ρ i ≠ 0 := sub_ne_zero.mpr (hs i)
  have hterm : 1 / (s - ρ i) + 1 / ρ i = s * (ρ i)⁻¹ * (s - ρ i)⁻¹ := by
    field_simp
    ring
  calc ‖1 / (s - ρ i) + 1 / ρ i‖
      = ‖s‖ * ‖(ρ i)⁻¹‖ * ‖(s - ρ i)⁻¹‖ := by rw [hterm, norm_mul, norm_mul]
    _ ≤ ‖s‖ * ‖(ρ i)⁻¹‖ * (2 * ‖(ρ i)⁻¹‖) := by gcongr
    _ = 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2 := by ring
theorem logDeriv_riemannXiCanonicalProduct_eq {s : ℂ}
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) s
      = ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i)
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hfne : ∀ i, f i s ≠ 0 := fun i ↦
    weierstrassE1_ne_zero (fun h ↦ hs i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h))
  have hlog : ∀ i, logDeriv (f i) s = 1 / (s - ρ i) + 1 / ρ i := fun i ↦
    logDeriv_weierstrassE1_div (riemannXiZeros_ne_zero i) (hs i)
  have hmsum : Summable (fun i ↦ logDeriv (f i) s) := by
    simp only [hlog]; exact summable_partial_fraction hs
  have htend : MultipliableLocallyUniformlyOn f Set.univ :=
    (hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ hsum).multipliableLocallyUniformlyOn
  have hnez : ∏' i, f i s ≠ 0 :=
    riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hs
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ s)
    hfne hd hmsum htend hnez
  exact hkey.trans (tsum_congr hlog)
theorem riemannXi_ne_zero_of_forall_ne {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    riemannXi s ≠ 0 := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  rw [hB s]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
    (riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros
      summable_inv_norm_sq_riemannXiZeros hs)
theorem logDeriv_riemannXi_eq {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have key : ∀ z : ℂ, (∀ i, z ≠ riemannXiZeros i) →
      logDeriv riemannXi z = B + ∑' i, (1 / (z - riemannXiZeros i) + 1 / riemannXiZeros i) := by
    intro z hz
    have hPne : riemannXiCanonicalProduct riemannXiZeros z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne _ summable_inv_norm_sq_riemannXiZeros hz
    have hξfun : riemannXi =
        fun w ↦ (1 / 2 * Complex.exp (B * w)) * riemannXiCanonicalProduct riemannXiZeros w := by
      funext w; rw [hB w]
    have hpre : (1 / 2 * Complex.exp (B * z) : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
    have hdpre : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * Complex.exp (B * w)) z := by
      fun_prop
    have hdP : DifferentiableAt ℂ (riemannXiCanonicalProduct riemannXiZeros) z :=
      differentiable_riemannXiCanonicalProduct _ summable_inv_norm_sq_riemannXiZeros z
    rw [hξfun, logDeriv_mul z hpre hPne hdpre hdP,
      logDeriv_riemannXiCanonicalProduct_eq hz]
    congr 1
    rw [logDeriv_const_mul z _ (by norm_num)]
    have hde : HasDerivAt (fun w : ℂ ↦ Complex.exp (B * w)) (Complex.exp (B * z) * B) z := by
      simpa using ((hasDerivAt_id z).const_mul (B : ℂ)).cexp
    rw [logDeriv_apply, hde.deriv, mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero _),
      mul_one]
  have h0 : ∀ i, (0 : ℂ) ≠ riemannXiZeros i := fun i ↦ (riemannXiZeros_ne_zero i).symm
  have htsum0 : ∑' i, (1 / ((0 : ℂ) - riemannXiZeros i) + 1 / riemannXiZeros i) = 0 := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero]
  have hkey0 := key 0 h0
  rw [htsum0, add_zero] at hkey0
  rw [key s hs, hkey0]
theorem logDeriv_riemannZeta_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannZeta s = logDeriv riemannXi 0 - 1 / s - 1 / (s - 1)
      + 1 / 2 * (Real.log π : ℂ) - 1 / 2 * Complex.digamma (s / 2)
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hre
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hsdiv : 0 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsdiv
  have hnp : ∀ m : ℕ, s / 2 ≠ -↑m := ne_neg_natCast_of_re_pos hsdiv
  have hdΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := differentiableAt_Gamma_of_re_pos hsdiv
  have hζne : riemannZeta s ≠ 0 := by
    intro h
    exact (riemannXi_ne_zero_of_forall_ne hs)
      (by rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓℝ, h, mul_zero])
  have hcpowne : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hf : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).neg).div_const 2
  have hcp : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := hf.const_cpow (Or.inl hπ)
  have hlcpow : logDeriv (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) := by
    rw [logDeriv_apply, hcp.deriv,
      show (π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)
        = (Complex.log π * (-1 / 2)) * (π : ℂ) ^ (-s / 2) by ring,
      mul_div_assoc, div_self hcpowne, mul_one, ← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hu : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hdΓfun : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) s :=
    hdΓ.comp s hu.differentiableAt
  have hcomp : logDeriv (Complex.Gamma ∘ fun w : ℂ ↦ w / 2) s
      = logDeriv Complex.Gamma (s / 2) * deriv (fun w : ℂ ↦ w / 2) s :=
    logDeriv_comp hdΓ hu.differentiableAt
  have hlΓ : logDeriv (fun w : ℂ ↦ Complex.Gamma (w / 2)) s
      = (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    rw [show (fun w : ℂ ↦ Complex.Gamma (w / 2)) = Complex.Gamma ∘ fun w ↦ w / 2 from rfl,
      hcomp, hu.deriv, ← Complex.digamma_def]
    ring
  have hdcpow : DifferentiableAt ℂ (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s := hcp.differentiableAt
  have hB' : logDeriv Gammaℝ s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2) := by
    rw [show (Gammaℝ : ℂ → ℂ) = fun w ↦ (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) from rfl,
      logDeriv_mul s hcpowne hΓne hdcpow hdΓfun, hlcpow, hlΓ]
  have hA : logDeriv (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s = 1 / s + 1 / (s - 1) := by
    have hda : HasDerivAt (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) (1 / 2 * (1 * (s - 1) + s * 1)) s :=
      ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).const_mul (1 / 2)
    rw [logDeriv_apply, hda.deriv]
    field_simp
  have hdΓℝ : DifferentiableAt ℂ Gammaℝ s := (Complex.analyticAt_Gammaℝ hre).differentiableAt
  have hdA' : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s := by fun_prop
  have hdf1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w) s := hdA'.mul hdΓℝ
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hAne : (1 / 2 * (s * (s - 1)) : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hsm1)
  have hf1ne : (1 / 2 * (s * (s - 1)) * Gammaℝ s : ℂ) ≠ 0 := mul_ne_zero hAne hΓℝ
  have hEq : riemannXi =ᶠ[nhds s]
      fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w := by
    have hV : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | w ≠ 1}) :=
      (Complex.isOpen_re_gt 0).inter isOpen_ne
    filter_upwards [hV.mem_nhds ⟨hre, hs1⟩] with w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hw0' : w ≠ 0 := by rintro rfl; simp at hw0
    exact riemannXi_eq_prefactor_mul hw0' hw1 (Gammaℝ_ne_zero_of_re_pos hw0)
  have hlogeq : logDeriv riemannXi s
      = logDeriv (fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
  have hxi1 : logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := logDeriv_riemannXi_eq hs
  have hxi2 : logDeriv riemannXi s = 1 / s + 1 / (s - 1)
      + (-(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2))
      + logDeriv riemannZeta s := by
    rw [hlogeq, logDeriv_mul s hf1ne hζne hdf1 hdζ, logDeriv_mul s hAne hΓℝ hdA' hdΓℝ, hA, hB']
  have heq := hxi2.symm.trans hxi1
  linear_combination heq
end
end CertificatePort27
section CertificatePort28
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
def bookerKernelDenom (m v τ : ℝ) : ℝ := (m ^ 2 - v ^ 2 - τ ^ 2) ^ 2 + 4 * m ^ 2 * v ^ 2
noncomputable def bookerRemainder (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ
lemma bookerKernelDenom_pos {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    0 < bookerKernelDenom m v τ :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)
lemma bookerRemainder_nonpos_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 0 := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerRemainder, ← neg_nonneg, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_nonneg (by norm_num)
  rintro u ⟨_, hu1⟩
  rw [← neg_div]
  exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) (by linarith)) (by nlinarith [sq_nonneg u])))
    (bookerKernelDenom_pos u hm hv).le
lemma bookerRemainder_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 1 / 2 :=
  (bookerRemainder_nonpos_of_dispersive hm hmv).trans (by norm_num)
lemma bookerKernelDenom_eq_mul (m v τ : ℝ) :
    bookerKernelDenom m v τ = ((m - τ) ^ 2 + v ^ 2) * ((m + τ) ^ 2 + v ^ 2) := by
  unfold bookerKernelDenom; ring
lemma bookerKernelDenom_partialFraction {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)
      = 2 * m / (m ^ 2 + v ^ 2)
        + 2 * τ ^ 2 * m * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
            / ((m ^ 2 + v ^ 2) * bookerKernelDenom m v τ) := by
  have hA : ((m - τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hB : ((m + τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
  have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
  rw [bookerKernelDenom_eq_mul]
  field_simp
  ring
noncomputable def bookerSinglePole (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, (1 - τ) *
    ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))
lemma bookerSinglePole_eq {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v = m / (m ^ 2 + v ^ 2) * (1 + bookerRemainder m v) := by
  have hint1 : IntervalIntegrable (fun τ : ℝ ↦ 2 * (1 - τ)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun τ : ℝ ↦ 2 * (1 - τ)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun τ : ℝ ↦
      2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by unfold bookerKernelDenom; fun_prop)
    exact fun τ ↦ (bookerKernelDenom_pos τ hm hv).ne'
  have hpt : Set.EqOn
      (fun τ : ℝ ↦ (1 - τ) *
        ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)))
      (fun τ : ℝ ↦ m / (m ^ 2 + v ^ 2) *
        (2 * (1 - τ) + 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
          / bookerKernelDenom m v τ))
      (Set.uIcc 0 1) := by
    intro τ _
    dsimp only
    have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
    have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
    rw [bookerKernelDenom_partialFraction τ hm hv]
    field_simp
  have h1 : ∫ τ in (0 : ℝ)..1, (2 : ℝ) * (1 - τ) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num
  unfold bookerSinglePole bookerRemainder
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hint1 hint2, h1]
lemma bookerSinglePole_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerSinglePole m v ≤ 3 / 2 * (m / (m ^ 2 + v ^ 2)) := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerSinglePole_eq hm hv]
  nlinarith [mul_le_mul_of_nonneg_left (bookerRemainder_le_of_dispersive hm hmv)
    (by positivity : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2))]
private lemma intervalIntegrable_log_add_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m + τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m) (b := m + 1)).comp_add_left m
  rwa [show m - m = (0 : ℝ) by ring, show m + 1 - m = (1 : ℝ) by ring] at h
private lemma intervalIntegrable_log_sub_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m - τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m - 1) (b := m)).comp_sub_left m
  rw [show m - (m - 1) = (1 : ℝ) by ring, show m - m = (0 : ℝ) by ring] at h
  exact h.symm
noncomputable def bookerSlice (m : ℝ) : ℝ :=
  (m + 1) * Real.log (m + 1) + (m - 1) * Real.log |m - 1| - 2 * m * Real.log m
lemma bookerSlice_eq_integral (m : ℝ) :
    bookerSlice m = ∫ τ in (0 : ℝ)..1, (Real.log (m + τ) - Real.log (m - τ)) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_log_add_left m)
    (intervalIntegrable_log_sub_left m)]
  have e1 : (∫ τ in (0 : ℝ)..1, Real.log (m + τ))
      = (m + 1) * Real.log (m + 1) - m * Real.log m - 1 := by
    rw [intervalIntegral.integral_comp_add_left Real.log m, add_zero, integral_log]; ring
  have e2 : (∫ τ in (0 : ℝ)..1, Real.log (m - τ))
      = m * Real.log m - (m - 1) * Real.log (m - 1) - 1 := by
    rw [intervalIntegral.integral_comp_sub_left Real.log m, sub_zero, integral_log]; ring
  rw [e1, e2, bookerSlice, Real.log_abs]; ring
lemma bookerSinglePole_eq_half_integral_log {m v : ℝ} (hv : v ≠ 0) :
    bookerSinglePole m v = ∫ τ in (0 : ℝ)..1,
      1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) := by
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  have hVderiv : ∀ τ : ℝ,
      HasDerivAt V ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) τ := by
    intro τ
    have hp : (m + τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hq : (m - τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hin1 : HasDerivAt (fun τ : ℝ ↦ (m + τ) ^ 2 + v ^ 2) (2 * (m + τ)) τ := by
      simpa using (((hasDerivAt_id τ).const_add m).pow 2).add_const (v ^ 2)
    have hin2 : HasDerivAt (fun τ : ℝ ↦ (m - τ) ^ 2 + v ^ 2) (2 * (m - τ) * (-1)) τ := by
      simpa using (((hasDerivAt_id τ).const_sub m).pow 2).add_const (v ^ 2)
    exact (HasDerivAt.const_mul (1 / 2) ((hin1.log hp).sub (hin2.log hq))).congr_deriv
      (by field_simp; ring)
  have hcont : Continuous
      (fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ ↦ 1 - s) (v := V) (u' := fun _ : ℝ ↦ (-1 : ℝ))
    (v' := fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))
    (fun x _ ↦ by simpa using (hasDerivAt_id x).const_sub 1) (fun x _ ↦ hVderiv x)
    (continuous_const.intervalIntegrable 0 1) (hcont.intervalIntegrable 0 1)
  have hV0 : V 0 = 0 := by simp [hVdef]
  rw [bookerSinglePole, hibp, intervalIntegral.integral_const_mul, hV0]
  ring
lemma bookerSinglePole_le_bookerSlice {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v ≤ bookerSlice m := by
  rw [bookerSinglePole_eq_half_integral_log hv, bookerSlice_eq_integral m]
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  have hVcont : Continuous V := by
    rw [hVdef]
    exact ((Continuous.log (by fun_prop) fun τ ↦ by positivity).sub
      (Continuous.log (by fun_prop) fun τ ↦ by positivity)).const_mul _
  refine intervalIntegral.integral_mono_ae_restrict (by norm_num)
    (hVcont.intervalIntegrable 0 1)
    ((intervalIntegrable_log_add_left m).sub (intervalIntegrable_log_sub_left m)) ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) m]
    with τ hτm hτmem
  obtain ⟨hτ0, hτ1⟩ := hτmem
  have hmt : (0 : ℝ) < m + τ := by linarith
  have hmtne : m - τ ≠ 0 := sub_ne_zero.mpr fun h ↦ hτm h.symm
  have hA : (0 : ℝ) < (m + τ) ^ 2 := by positivity
  have hB : (0 : ℝ) < (m - τ) ^ 2 := by positivity
  have hAB : (m - τ) ^ 2 ≤ (m + τ) ^ 2 := by nlinarith [mul_nonneg hm.le hτ0]
  have hfrac : ((m + τ) ^ 2 + v ^ 2) / (m + τ) ^ 2 ≤ ((m - τ) ^ 2 + v ^ 2) / (m - τ) ^ 2 := by
    rw [div_le_div_iff₀ hA hB]; nlinarith [mul_le_mul_of_nonneg_left hAB (sq_nonneg v)]
  have hlog := Real.log_le_log (by positivity) hfrac
  rw [Real.log_div (by positivity) hA.ne', Real.log_div (by positivity) hB.ne',
    Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith [hlog]
noncomputable def bookerSinglePoleIntegral (a v : ℝ) : ℝ :=
  ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2))
lemma bookerSinglePoleIntegral_eq {a v : ℝ} (hv : v ≠ 0) :
    bookerSinglePoleIntegral a v = bookerSinglePole (1 - a) v := by
  unfold bookerSinglePoleIntegral bookerSinglePole
  set f : ℝ → ℝ := fun ρ ↦ (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2)) with hf
  set h : ℝ → ℝ := fun τ ↦ (1 - |τ|) * ((1 - a + τ) / ((1 - a + τ) ^ 2 + v ^ 2)) with hh
  have hch : Continuous h := by
    rw [hh]
    exact Continuous.mul (by fun_prop)
      (Continuous.div (by fun_prop) (by fun_prop) fun x ↦ by positivity)
  have hcn : Continuous (fun τ ↦ h (-τ)) := hch.comp continuous_neg
  have hstep : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ ρ in (0 : ℝ)..2, f ρ := by
    rw [intervalIntegral.integral_comp_add_right f 1]; norm_num
  have hcongr : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ τ in (-1 : ℝ)..1, h τ :=
    intervalIntegral.integral_congr (fun τ _ ↦ by
      simp only [hf, hh]
      rw [show (1 : ℝ) - (τ + 1) = -τ by ring, abs_neg]; ring)
  rw [← hstep, hcongr]
  have hneg : (∫ τ in (-1 : ℝ)..0, h τ) = ∫ τ in (0 : ℝ)..1, h (-τ) := by
    rw [intervalIntegral.integral_comp_neg h]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hch.intervalIntegrable (-1) 0) (hch.intervalIntegrable 0 1), hneg,
      ← intervalIntegral.integral_add (hcn.intervalIntegrable 0 1) (hch.intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr (fun τ hτ ↦ ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  obtain ⟨hτ0, _⟩ := hτ
  simp only [hh, abs_neg, abs_of_nonneg hτ0]
  ring
open intervalIntegral MeasureTheory Topology in
lemma intervalIntegral.integral_integral_add_eq_tent {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ := by
  set F : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, f t with hF_def
  have hFderiv : ∀ x : ℝ, HasDerivAt F (f x) x := fun x ↦
    integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
      (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
  have hFcont : Continuous F := Differentiable.continuous fun x ↦ (hFderiv x).differentiableAt
  set G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, F t with hG_def
  have e0 : (∫ σ in (0 : ℝ)..1, F σ) = G 1 := by simp only [hG_def]
  have hFG2 : (∫ ρ in (1 : ℝ)..2, F ρ) = G 2 - G 1 := by
    simp only [hG_def]
    linarith [integral_add_adjacent_intervals (hFcont.intervalIntegrable (μ := volume) 0 1)
      (hFcont.intervalIntegrable 1 2)]
  have hinner : ∀ σ : ℝ, (∫ r in (0 : ℝ)..1, f (r + σ)) = F (1 + σ) - F σ := fun σ ↦ by
    rw [integral_comp_add_right f σ, zero_add]
    simp only [hF_def]
    linarith [integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) 0 σ)
      (hf.intervalIntegrable σ (1 + σ))]
  have e1 : (∫ σ in (0 : ℝ)..1, F (1 + σ)) = G 2 - G 1 := by
    rw [integral_congr (g := fun σ ↦ F (σ + 1)) fun σ _ ↦ by rw [add_comm],
      integral_comp_add_right F 1, zero_add, (by norm_num : (1 : ℝ) + 1 = 2), hFG2]
  have hc1 : IntervalIntegrable (fun σ : ℝ ↦ F (1 + σ)) volume 0 1 :=
    (hFcont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  have hLHS : (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ)) = G 2 - 2 * G 1 := by
    rw [integral_congr (fun σ _ ↦ hinner σ),
      integral_sub hc1 (hFcont.intervalIntegrable 0 1), e1, e0]
    ring
  have htent : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * f ρ) := by fun_prop
  have hsplit : (∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ)
      = (∫ ρ in (0 : ℝ)..1, ρ * f ρ) + ∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ := by
    rw [← integral_add_adjacent_intervals (htent.intervalIntegrable 0 1)
      (htent.intervalIntegrable 1 2)]
    congr 1
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hρ
      rw [abs_of_nonneg (by linarith [hρ.2] : (0 : ℝ) ≤ 1 - ρ)]; ring
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hρ
      rw [abs_of_nonpos (by linarith [hρ.1] : 1 - ρ ≤ 0)]; ring
  have hIBP1 : (∫ ρ in (0 : ℝ)..1, ρ * f ρ) = F 1 - G 1 := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (u := fun ρ ↦ ρ) (v := F) (u' := fun _ ↦ (1 : ℝ)) (v' := f)
      (fun x _ ↦ hasDerivAt_id x) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 0 1) (hf.intervalIntegrable 0 1)
    simp only [one_mul, zero_mul, sub_zero] at h ⊢
    rw [h, e0]
  have hIBP2 : (∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ) = -F 1 + (G 2 - G 1) := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := 2)
      (u := fun ρ ↦ 2 - ρ) (v := F) (u' := fun _ ↦ (-1 : ℝ)) (v' := f)
      (fun x _ ↦ (hasDerivAt_id x).const_sub 2) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 1 2) (hf.intervalIntegrable 1 2)
    beta_reduce at h
    rw [h, show (∫ x in (1 : ℝ)..2, (-1 : ℝ) * F x) = -(G 2 - G 1) from by
      rw [intervalIntegral.integral_const_mul, hFG2]; ring]
    ring
  rw [hLHS, hsplit, hIBP1, hIBP2]
  ring
open intervalIntegral MeasureTheory in
lemma integral_integral_eq_bookerSinglePoleIntegral_add {u v : ℝ} (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
  have habs : Continuous (fun ρ : ℝ ↦ 1 - |1 - ρ|) := by fun_prop
  have hcont : Continuous (fun s : ℝ ↦
      (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity))
  have hk1 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - -u) / ((ρ - -u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  have hk2 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - u) / ((ρ - u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  calc (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) *
          ((ρ + u) / ((ρ + u) ^ 2 + v ^ 2) + (ρ - u) / ((ρ - u) ^ 2 + v ^ 2)) :=
        intervalIntegral.integral_integral_add_eq_tent hcont
    _ = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
        unfold bookerSinglePoleIntegral
        rw [← integral_add (hk1.intervalIntegrable 0 2) (hk2.intervalIntegrable 0 2)]
        refine integral_congr (fun ρ _ ↦ ?_)
        ring
noncomputable def bookerSliceReciprocal (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - (x - 1) * Real.log |x - 1|
lemma bookerSliceReciprocal_eq_sub (x : ℝ) :
    bookerSliceReciprocal x = (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) := by
  rw [bookerSliceReciprocal, Real.log_abs]
private lemma hasDerivAt_log_add_one {x : ℝ} (h : x + 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y + 1)) (x + 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).add_const 1)
private lemma hasDerivAt_log_sub_one {x : ℝ} (h : x - 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y - 1)) (x - 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).sub_const 1)
private lemma hasDerivAt_bookerSliceReciprocal {x : ℝ} (h1 : x + 1 ≠ 0) (h2 : x - 1 ≠ 0) :
    HasDerivAt bookerSliceReciprocal (Real.log (x + 1) - Real.log (x - 1)) x := by
  rw [funext bookerSliceReciprocal_eq_sub]
  have d1 : HasDerivAt (fun x : ℝ ↦ x + 1) 1 x := (hasDerivAt_id x).add_const 1
  have d2 : HasDerivAt (fun x : ℝ ↦ x - 1) 1 x := (hasDerivAt_id x).sub_const 1
  exact ((d1.mul (hasDerivAt_log_add_one h1)).sub (d2.mul (hasDerivAt_log_sub_one h2))).congr_deriv
    (by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]; ring)
private lemma deriv_bookerSliceReciprocal_eqOn {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv bookerSliceReciprocal =ᶠ[nhds x] fun y ↦ Real.log (y + 1) - Real.log (y - 1) :=
  Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦
    (hasDerivAt_bookerSliceReciprocal (hUmem y hy).1 (hUmem y hy).2).deriv
private lemma hasDerivAt_deriv_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (deriv bookerSliceReciprocal) ((x + 1)⁻¹ - (x - 1)⁻¹) x := by
  have heq := deriv_bookerSliceReciprocal_eqOn hU hUmem hx
  exact (((hasDerivAt_log_add_one (hUmem x hx).1).sub
    (hasDerivAt_log_sub_one (hUmem x hx).2)).congr_of_eventuallyEq heq)
private lemma deriv2_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv^[2] bookerSliceReciprocal x = (x + 1)⁻¹ - (x - 1)⁻¹ := by
  change deriv (deriv bookerSliceReciprocal) x = _
  exact (hasDerivAt_deriv_bookerSliceReciprocal hU hUmem hx).deriv
private lemma continuous_bookerSliceReciprocal_form :
    Continuous fun x : ℝ ↦ (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) :=
  (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x + 1)).sub
    (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x - 1))
private lemma continuousOn_bookerSliceReciprocal (S : Set ℝ) :
    ContinuousOn bookerSliceReciprocal S :=
  continuous_bookerSliceReciprocal_form.continuousOn.congr fun x _ ↦
    bookerSliceReciprocal_eq_sub x
private lemma convexOn_bookerSliceReciprocal :
    ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioo (1 / 2 : ℝ) 1, y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by linarith [hy.1]), ne_of_lt (by linarith [hy.2])⟩
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioo hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioo hUmem hx]
    have hna : (x - 1)⁻¹ < 0 := inv_lt_zero.mpr (by linarith [hx.2])
    have hpb : (0 : ℝ) < (x + 1)⁻¹ := inv_pos.mpr (by linarith [hx.1])
    linarith
private lemma concaveOn_bookerSliceReciprocal :
    ConcaveOn ℝ (Set.Ici (1 : ℝ)) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioi (1 : ℝ), y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith),
      ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith)⟩
  apply concaveOn_of_deriv2_nonpos (convex_Ici _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioi hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioi hUmem hx, sub_nonpos]
    simp only [Set.mem_Ioi] at hx
    have ha : 0 < x - 1 := by linarith
    exact inv_anti₀ ha (by linarith)
private lemma le_add_deriv_mul_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} {x x₀ f' : ℝ}
    (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (hx₀ : x₀ ∈ S) (hd : HasDerivAt f f' x₀) :
    f x ≤ f x₀ + f' * (x - x₀) := by
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · have hslope := hf.le_slope_of_hasDerivAt hx hx₀ hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith : (0 : ℝ) < x₀ - x)] at hslope
    nlinarith [hslope]
  · rw [heq]; simp
  · have hslope := hf.slope_le_of_hasDerivAt hx₀ hx hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith : (0 : ℝ) < x - x₀)] at hslope
    nlinarith [hslope]
lemma bookerSliceReciprocal_le {x : ℝ} (hx : 1 / 2 ≤ x) :
    bookerSliceReciprocal x ≤ 3 / 2 * x ^ 2 := by
  have hl2l := Real.log_two_gt_d9
  have hl2u := Real.log_two_lt_d9
  have hl3l := Real.log_three_gt_d9
  have hl3u := Real.log_three_lt_d9
  have hl5l := Real.log_five_gt_d9
  have hl5u := Real.log_five_lt_d9
  rcases le_total x 1 with hx1 | hx1
  ·
    have hmem_half : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have hmem_one : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have ha : (0 : ℝ) ≤ 2 * (1 - x) := by linarith
    have hb : (0 : ℝ) ≤ 2 * x - 1 := by linarith
    have hab : 2 * (1 - x) + (2 * x - 1) = 1 := by ring
    have hchord := convexOn_bookerSliceReciprocal.2 hmem_half hmem_one ha hb hab
    simp only [smul_eq_mul] at hchord
    rw [show 2 * (1 - x) * (1 / 2) + (2 * x - 1) * 1 = x by ring] at hchord
    have e_half : bookerSliceReciprocal (1 / 2) = 3 / 2 * Real.log 3 - 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show |(1 : ℝ) / 2 - 1| = 1 / 2 by
          rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, abs_neg]; norm_num,
        show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one]
      ring
    have e_one : bookerSliceReciprocal 1 = 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
      simp only [abs_zero, Real.log_zero, mul_zero, sub_zero]
    rw [e_half, e_one] at hchord
    nlinarith [hchord, sq_nonneg (x - (8 * Real.log 2 - 3 * Real.log 3) / 3),
      hl2l, hl2u, hl3l, hl3u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 3 - 1.0986122885)
        (by linarith : (0 : ℝ) ≤ (0.6931471808 : ℝ) - Real.log 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803)
        (by linarith : (0 : ℝ) ≤ (1.0986122888 : ℝ) - Real.log 3)]
  ·
    have hx0mem : (13 / 12 : ℝ) ∈ Set.Ici (1 : ℝ) := by norm_num
    have hxmem : x ∈ Set.Ici (1 : ℝ) := hx1
    have hderiv : HasDerivAt bookerSliceReciprocal
        (Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1)) (13 / 12) :=
      hasDerivAt_bookerSliceReciprocal (by norm_num) (by norm_num)
    have eL' : Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1) = 2 * Real.log 5 := by
      rw [show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num, show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        ← Real.log_div (by norm_num) (by norm_num),
        show (25 : ℝ) / 12 / (1 / 12) = 25 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.log_pow]
      push_cast; ring
    have eL0 : bookerSliceReciprocal (13 / 12)
        = 25 / 6 * Real.log 5 - 4 * Real.log 2 - 2 * Real.log 3 := by
      rw [bookerSliceReciprocal_eq_sub, show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num,
        show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one, show (25 : ℝ) = 5 ^ 2 by norm_num, show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
        Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      push_cast; ring
    rw [eL'] at hderiv
    have htan : bookerSliceReciprocal x
        ≤ bookerSliceReciprocal (13 / 12) + 2 * Real.log 5 * (x - 13 / 12) :=
      le_add_deriv_mul_of_concaveOn concaveOn_bookerSliceReciprocal hxmem hx0mem hderiv
    rw [eL0] at htan
    nlinarith [htan, sq_nonneg (x - 2 * Real.log 5 / 3), hl2l, hl2u, hl3l, hl5l, hl5u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 5 - 1.6094379123)
        (by linarith : (0 : ℝ) ≤ (1.6094379126 : ℝ) - Real.log 5)]
lemma bookerSlice_eq_mul_bookerSliceReciprocal {m : ℝ} (hm : 0 < m) :
    bookerSlice m = m * bookerSliceReciprocal (1 / m) := by
  have hm0 : m ≠ 0 := hm.ne'
  rcases eq_or_ne m 1 with rfl | hm1
  · norm_num [bookerSlice, bookerSliceReciprocal]
  · have hlm : Real.log (1 / m + 1) = Real.log (m + 1) - Real.log m := by
      rw [show (1 : ℝ) / m + 1 = (m + 1) / m by field_simp; ring, Real.log_div (by positivity) hm0]
    have habs : |m - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hm1)
    have hlm2 : Real.log |1 / m - 1| = Real.log |m - 1| - Real.log m := by
      rw [show |(1 : ℝ) / m - 1| = |m - 1| / m by
            rw [show (1 : ℝ) / m - 1 = (1 - m) / m by field_simp, abs_div, abs_of_pos hm,
              abs_sub_comm],
        Real.log_div habs hm0]
    rw [bookerSlice, bookerSliceReciprocal, hlm, hlm2]
    field_simp
    ring
lemma mul_bookerSlice_le {m : ℝ} (hm0 : 0 < m) (hm2 : m ≤ 2) :
    m * bookerSlice m ≤ 3 / 2 := by
  have hx : (1 : ℝ) / 2 ≤ 1 / m := by rw [le_div_iff₀ hm0]; linarith
  rw [bookerSlice_eq_mul_bookerSliceReciprocal hm0]
  nlinarith [mul_le_mul_of_nonneg_left (bookerSliceReciprocal_le hx) (sq_nonneg m),
    (by field_simp : m ^ 2 * (1 / m) ^ 2 = 1)]
lemma bookerSinglePole_le_of {m v : ℝ} (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePole m v ≤ c * (m / (m ^ 2 + v ^ 2)) := by
  rcases hm0.lt_or_eq with hm | rfl
  · rcases le_or_gt (m ^ 2) (3 * v ^ 2) with hd | hconc
    ·
      have hdisp := bookerSinglePole_le_of_dispersive hm hd
      have hpos : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2) := by positivity
      exact le_trans hdisp (mul_le_mul_of_nonneg_right (by linarith) hpos)
    ·
      have hP : bookerSinglePole m v ≤ bookerSlice m := bookerSinglePole_le_bookerSlice hm hv
      have hΦ : m * bookerSlice m ≤ 3 / 2 := mul_bookerSlice_le hm hm2
      have hmv2 : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
      have hB : bookerSlice m ≤ 3 / (2 * m) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)]; nlinarith [hΦ]
      have hD : (3 : ℝ) / (2 * m) ≤ c * (m / (m ^ 2 + v ^ 2)) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m),
          show c * (m / (m ^ 2 + v ^ 2)) * (2 * m) = 2 * c * m ^ 2 / (m ^ 2 + v ^ 2) by ring,
          le_div_iff₀ hmv2]
        nlinarith [hconc.le, mul_nonneg (show (0 : ℝ) ≤ c - 2 by linarith) (mul_pos hm hm).le]
      exact le_trans (le_trans hP hB) hD
  ·
    have h0 : bookerSinglePole 0 v = 0 := by
      rw [bookerSinglePole, intervalIntegral.integral_congr (g := fun _ : ℝ ↦ (0 : ℝ))
        (fun τ _ ↦ by
          rw [show (0 : ℝ) + τ = τ by ring, show (0 : ℝ) - τ = -τ by ring, neg_sq]; ring),
        intervalIntegral.integral_zero]
    rw [h0]
    simp
theorem bookerSinglePoleIntegral_le_of {a v : ℝ} (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePoleIntegral a v ≤ c * ((1 - a) / ((1 - a) ^ 2 + v ^ 2)) := by
  rw [bookerSinglePoleIntegral_eq hv]
  exact bookerSinglePole_le_of (by linarith) (by linarith) hv hc
noncomputable def bookerPairKernel (u v s : ℝ) : ℝ :=
  (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)
noncomputable def bookerPairIntegral (d : ℝ) (w : ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..d, Real.log ‖((x : ℂ) + (d : ℂ) + w) *
    ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
    (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖
theorem bookerPairKernel_integral_le_of {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (r + σ))
      ≤ c * bookerPairKernel u v 1 := by
  unfold bookerPairKernel
  rw [integral_integral_eq_bookerSinglePoleIntegral_add hv]
  have h1 := bookerSinglePoleIntegral_le_of (a := -u) (v := v) (by linarith) (by linarith) hv hc
  have h2 := bookerSinglePoleIntegral_le_of (a := u) (v := v) (by linarith) (by linarith) hv hc
  simp only [sub_neg_eq_add] at h1
  rw [mul_add]
  linarith
private lemma bookerPairKernel_abs (u v s : ℝ) :
    bookerPairKernel u v s = bookerPairKernel |u| v s := by
  unfold bookerPairKernel
  rcases abs_choice u with h | h
  · rw [h]
  · rw [h]; ring
private lemma bookerPairKernel_scale (u v s d : ℝ) (hd : d ≠ 0) (hv : v ≠ 0) :
    bookerPairKernel u v (d * s) = 1 / d * bookerPairKernel (u / d) (v / d) s := by
  have h1 : (d * s + u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h2 : (d * s - u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h3 : (s + u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  have h4 : (s - u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  unfold bookerPairKernel
  rw [show d * s + u = d * (s + u / d) by field_simp,
    show d * s - u = d * (s - u / d) by field_simp]
  field_simp
private lemma Complex.log_norm_eq_half_log (z : ℂ) :
    Real.log ‖z‖ = 1 / 2 * Real.log (z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply, ← sq, ← sq]
  ring
private lemma integral_pole_add (x d v b : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ + b) / ((x + σ + b) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d + b) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x + b) ^ 2 + v ^ 2) := by
  have hpos : ∀ s : ℝ, (0 : ℝ) < (x + s + b) ^ 2 + v ^ 2 := fun s ↦ by positivity
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) d,
      HasDerivAt (fun y ↦ 1 / 2 * Real.log ((x + y + b) ^ 2 + v ^ 2))
        ((x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) s := by
    intro s _
    have hlin : HasDerivAt (fun y ↦ x + y + b) 1 s := by
      simpa using ((hasDerivAt_id s).const_add x).add_const b
    have hsq : HasDerivAt (fun y ↦ (x + y + b) ^ 2 + v ^ 2) (2 * (x + s + b)) s := by
      simpa using (hlin.pow 2).add_const (v ^ 2)
    exact ((hsq.log (hpos s).ne').const_mul (1 / 2)).congr_deriv (by ring)
  have hcont : Continuous (fun s ↦ (x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ ne_of_gt (hpos s))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]; norm_num
private lemma integral_pole_sub (x d v a : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d - a) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x - a) ^ 2 + v ^ 2) := by
  rw [show (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
        = ∫ σ in (0 : ℝ)..d, (x + σ + (-a)) / ((x + σ + (-a)) ^ 2 + v ^ 2) from
      intervalIntegral.integral_congr (fun σ _ ↦ by ring_nf), integral_pole_add x d v (-a) hv]
  ring_nf
private lemma double_integral_bookerPairKernel_scale {d u v : ℝ} (hd : 0 < d) (hv : v ≠ 0) :
    (∫ x in (0 : ℝ)..d, ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))
      = d * ∫ x in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (x + σ) := by
  have subst : ∀ (f : ℝ → ℝ), (∫ y in (0 : ℝ)..d, f y) = d * ∫ y in (0 : ℝ)..1, f (d * y) := by
    intro f
    rw [intervalIntegral.integral_comp_mul_left f hd.ne', mul_zero, mul_one, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  rw [subst (fun x ↦ ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ d * ∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        (fun y _ ↦ subst (fun σ ↦ bookerPairKernel u v (d * y + σ)))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ))
        (fun y _ ↦ ?_)]
  · rw [intervalIntegral.integral_const_mul]; field_simp
  · change (∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        = 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun σ _ ↦ ?_)
    rw [show d * y + d * σ = d * (y + σ) by ring, bookerPairKernel_scale u v (y + σ) d hd.ne' hv]
private lemma bookerPairKernel_integral_le_of_abs_le {u v : ℝ} (hu : |u| ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
      ≤ c * bookerPairKernel u v 1 := by
  have key := bookerPairKernel_integral_le_of (abs_nonneg u) hu hv hc
  rw [show (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
        = ∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel |u| v (r + σ) from
      intervalIntegral.integral_congr (fun σ _ ↦
        intervalIntegral.integral_congr (fun r _ ↦ by
          rw [bookerPairKernel_abs u v (σ + r), add_comm σ r]))]
  rw [bookerPairKernel_abs u v 1]
  exact key
theorem bookerPairIntegral_le_of {d : ℝ} (hd1 : 1 / 2 < d) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) (hwim : w.im ≠ 0) {c : ℝ} (hc : 2 ≤ c) :
    bookerPairIntegral d w
      ≤ c * d ^ 2 * (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re := by
  unfold bookerPairIntegral
  have hd0 : 0 < d := by linarith
  have hre : (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re
      = bookerPairKernel w.re w.im d := by
    unfold bookerPairKernel
    simp only [Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, one_div]
    ring
  have hint : ∀ x : ℝ,
      Real.log ‖((x : ℂ) + (d : ℂ) + w) * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
        (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖
        = ∫ σ in (0 : ℝ)..d, bookerPairKernel w.re w.im (x + σ) := by
    intro x
    have hz : ∀ z : ℂ, z.im ≠ 0 → z ≠ 0 := fun z hz h ↦ hz (by rw [h]; simp)
    have hA : ((x : ℂ) + (d : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hB : ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    have hC : ((x : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hD : ((x : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    rw [norm_div, norm_mul, norm_mul,
        Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB))
                     (mul_ne_zero (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD)),
        Real.log_mul (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB),
        Real.log_mul (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD),
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log,
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    unfold bookerPairKernel
    rw [intervalIntegral.integral_add, integral_pole_add x d w.im w.re hwim,
        integral_pole_sub x d w.im w.re hwim]
    · ring_nf
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
  rw [hre, intervalIntegral.integral_congr (fun x _ ↦ hint x),
      double_integral_bookerPairKernel_scale hd0 hwim]
  have hRHS : c * d ^ 2 * bookerPairKernel w.re w.im d
      = d * (c * bookerPairKernel (w.re / d) (w.im / d) 1) := by
    have hs := bookerPairKernel_scale w.re w.im 1 d hd0.ne' hwim
    rw [mul_one] at hs
    rw [hs]; field_simp
  rw [hRHS]
  apply mul_le_mul_of_nonneg_left _ hd0.le
  refine bookerPairKernel_integral_le_of_abs_le ?_ ?_ hc
  · rw [abs_div, abs_of_pos hd0, div_le_one hd0]; linarith
  · exact div_ne_zero hwim hd0.ne'
end
end CertificatePort28
section CertificatePort29
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open scoped Topology
variable {a b : ℝ}
def IsContLog (a b : ℝ) (φ g : ℝ → ℂ) : Prop :=
  ContinuousOn g (Set.Icc a b) ∧ ∀ u ∈ Set.Icc a b, Complex.exp (g u) = φ u
namespace IsContLog
theorem continuousOn {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) :
    ContinuousOn φ (Set.Icc a b) :=
  (Complex.continuous_exp.comp_continuousOn hg.1).congr fun u hu => (hg.2 u hu).symm
theorem ne_zero {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) {u : ℝ} (hu : u ∈ Set.Icc a b) :
    φ u ≠ 0 := by
  rw [← hg.2 u hu]; exact Complex.exp_ne_zero _
end IsContLog
theorem simplyConnectedSpace_Icc (hab : a ≤ b) :
    SimplyConnectedSpace ↥(Set.Icc a b) := by
  have : ContractibleSpace ↥(Set.Icc a b) :=
    (convex_Icc a b).contractibleSpace ⟨a, Set.left_mem_Icc.mpr hab⟩
  infer_instance
instance instLocallyPathConnectedSpaceIcc :
    LocallyPathConnectedSpace ↥(Set.Icc a b) :=
  (convex_Icc a b).locallyPathConnectedSpace
theorem exists_isContLog (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    {c : ℂ} (hc : Complex.exp c = φ a) :
    ∃ g : ℝ → ℂ, IsContLog a b φ g ∧ g a = c := by
  have := simplyConnectedSpace_Icc hab
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, hφ.domRestrict⟩
  have hs : ∀ x : ↥(Set.Icc a b), f x ∈ ({0}ᶜ : Set ℂ) := fun x =>
    Set.mem_compl_singleton_iff.mpr (h0 x.1 x.2)
  have he : Complex.exp c = f ⟨a, Set.left_mem_Icc.mpr hab⟩ := hc
  obtain ⟨F, ⟨hFa, hFp⟩, -⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  refine ⟨fun u => F (Set.projIcc a b hab u), ⟨?_, ?_⟩, ?_⟩
  · exact (F.continuous.comp continuous_projIcc).continuousOn
  · intro u hu
    change Complex.exp (F (Set.projIcc a b hab u)) = φ u
    have hcong := congrFun hFp (Set.projIcc a b hab u)
    simp only [Function.comp_apply] at hcong
    rw [hcong, Set.projIcc_of_mem hab hu]
    rfl
  · change F (Set.projIcc a b hab a) = c
    rw [Set.projIcc_of_mem hab (Set.left_mem_Icc.mpr hab)]
    exact hFa
theorem exists_isContLog_of_ne_zero (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    ∃ g, IsContLog a b φ g :=
  let ⟨g, hg, _⟩ := exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  ⟨g, hg⟩
theorem IsContLog.sub_const (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    ∀ u ∈ Set.Icc a b, g₁ u - g₂ u = g₁ a - g₂ a := by
  have := simplyConnectedSpace_Icc hab
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  set k : ℂ := g₁ a - g₂ a with hk
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, h1.continuousOn.domRestrict⟩
  let F₁ : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict g₁, h1.1.domRestrict⟩
  let F₂ : C(↥(Set.Icc a b), ℂ) :=
    ⟨fun x => (Set.Icc a b).domRestrict g₂ x + k, (h2.1.domRestrict).add continuous_const⟩
  have hexpk : Complex.exp k = 1 := by
    rw [hk, Complex.exp_sub, h1.2 a hamem, h2.2 a hamem, div_self (h1.ne_zero hamem)]
  have hP1 : F₁ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₁ = ⇑f := by
    refine ⟨rfl, funext fun x => ?_⟩
    simpa [F₁, f] using h1.2 x.1 x.2
  have hP2 : F₂ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₂ = ⇑f := by
    refine ⟨by simp only [F₂, ContinuousMap.coe_mk, Set.domRestrict_apply, hk]; ring,
      funext fun x => ?_⟩
    simp only [F₂, f, Function.comp_apply, ContinuousMap.coe_mk, Set.domRestrict_apply,
      Complex.exp_add, hexpk, mul_one]
    exact h2.2 x.1 x.2
  have huniq := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (e₀ := g₁ a) (a₀ := ⟨a, hamem⟩) (h1.2 a hamem)
    (fun x => Set.mem_compl_singleton_iff.mpr (h1.ne_zero x.2))
  have hF : F₁ = F₂ := huniq.unique hP1 hP2
  intro u hu
  have := DFunLike.congr_fun hF ⟨u, hu⟩
  simp only [F₁, F₂, ContinuousMap.coe_mk, Set.domRestrict_apply] at this
  rw [this]; ring
theorem IsContLog.im_sub_eq (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    (g₁ b).im - (g₁ a).im = (g₂ b).im - (g₂ a).im := by
  have key := h1.sub_const hab h2 b (Set.right_mem_Icc.mpr hab)
  have hsub : (g₁ b - g₂ b).im = (g₁ a - g₂ a).im := by rw [key]
  simp only [Complex.sub_im] at hsub
  linarith
open Classical in
noncomputable def argVariation (a b : ℝ) (φ : ℝ → ℂ) : ℝ :=
  if h : ∃ g, IsContLog a b φ g then (h.choose b).im - (h.choose a).im else 0
theorem argVariation_eq_of_isContLog (hab : a ≤ b) {φ g : ℝ → ℂ}
    (hg : IsContLog a b φ g) : argVariation a b φ = (g b).im - (g a).im := by
  have hex : ∃ g, IsContLog a b φ g := ⟨g, hg⟩
  rw [argVariation, dif_pos hex]
  exact IsContLog.im_sub_eq hab hex.choose_spec hg
theorem argVariation_congr (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (h : Set.EqOn φ ψ (Set.Icc a b)) : argVariation a b φ = argVariation a b ψ := by
  by_cases hex : ∃ g, IsContLog a b φ g
  · obtain ⟨g, hg⟩ := hex
    have hg' : IsContLog a b ψ g := ⟨hg.1, fun u hu => (hg.2 u hu).trans (h hu)⟩
    rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog hab hg']
  · have hex' : ¬ ∃ g, IsContLog a b ψ g := fun ⟨g, hg⟩ =>
      hex ⟨g, hg.1, fun u hu => (hg.2 u hu).trans (h hu).symm⟩
    unfold argVariation
    rw [dif_neg hex, dif_neg hex']
theorem argVariation_mul (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0φ : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hψ : ContinuousOn ψ (Set.Icc a b)) (h0ψ : ∀ u ∈ Set.Icc a b, ψ u ≠ 0) :
    argVariation a b (φ * ψ) = argVariation a b φ + argVariation a b ψ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0φ
  obtain ⟨h, hh⟩ := exists_isContLog_of_ne_zero hab hψ h0ψ
  have hgh : IsContLog a b (φ * ψ) (g + h) := by
    refine ⟨hg.1.add hh.1, fun u hu => ?_⟩
    simp only [Pi.add_apply, Complex.exp_add, hg.2 u hu, hh.2 u hu, Pi.mul_apply]
  rw [argVariation_eq_of_isContLog hab hgh, argVariation_eq_of_isContLog hab hg,
    argVariation_eq_of_isContLog hab hh]
  simp only [Pi.add_apply, Complex.add_im]
  ring
theorem argVariation_trans {m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b φ = argVariation a m φ + argVariation m b φ := by
  have hab : a ≤ b := ham.trans hmb
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hsub_am : Set.Icc a m ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hmb
  have hsub_mb : Set.Icc m b ⊆ Set.Icc a b := Set.Icc_subset_Icc ham le_rfl
  have hg_am : IsContLog a m φ g := ⟨hg.1.mono hsub_am, fun u hu => hg.2 u (hsub_am hu)⟩
  have hg_mb : IsContLog m b φ g := ⟨hg.1.mono hsub_mb, fun u hu => hg.2 u (hsub_mb hu)⟩
  rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog ham hg_am,
    argVariation_eq_of_isContLog hmb hg_mb]
  ring
theorem argVariation_reverse (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => φ (a + b - u)) = - argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hmap : Set.MapsTo (fun u : ℝ => a + b - u) (Set.Icc a b) (Set.Icc a b) := by
    intro u hu
    simp only [Set.mem_Icc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hcont : Continuous (fun u : ℝ => a + b - u) := by fun_prop
  have hg' : IsContLog a b (fun u => φ (a + b - u)) (fun u => g (a + b - u)) := by
    refine ⟨hg.1.comp hcont.continuousOn hmap, fun u hu => hg.2 (a + b - u) (hmap hu)⟩
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  rw [show a + b - b = a by ring, show a + b - a = b by ring]
  ring
theorem argVariation_comp {a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    {σ : ℝ → ℝ} (hσc : ContinuousOn σ (Set.Icc a' b'))
    (hσmap : Set.MapsTo σ (Set.Icc a' b') (Set.Icc a b))
    (hσa : σ a' = a) (hσb : σ b' = b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a' b' (fun v => φ (σ v)) = argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hg' : IsContLog a' b' (fun v => φ (σ v)) (fun v => g (σ v)) :=
    ⟨hg.1.comp hσc hσmap, fun v hv => hg.2 (σ v) (hσmap hv)⟩
  rw [argVariation_eq_of_isContLog hab' hg', argVariation_eq_of_isContLog hab hg, hσa, hσb]
theorem argVariation_eq_arg_sub_arg (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (hsp : ∀ u ∈ Set.Icc a b, φ u ∈ Complex.slitPlane) :
    argVariation a b φ = (φ b).arg - (φ a).arg := by
  have hlog : IsContLog a b φ (fun u => Complex.log (φ u)) :=
    ⟨hφ.clog hsp, fun u hu => Complex.exp_log (Complex.slitPlane_ne_zero (hsp u hu))⟩
  rw [argVariation_eq_of_isContLog hab hlog, Complex.log_im, Complex.log_im]
private theorem injOn_exp_ball (z₀ : ℂ) :
    Set.InjOn Complex.exp (Metric.ball z₀ Real.pi) := by
  intro z hz w hw hzw
  have h1 : Complex.exp (z - w) = 1 := by
    rw [Complex.exp_sub, hzw, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hd : ‖z - w‖ < 2 * Real.pi := by
    calc ‖z - w‖ = ‖(z - z₀) - (w - z₀)‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖w - z₀‖ := norm_sub_le _ _
      _ < Real.pi + Real.pi := by
          rw [mem_ball_iff_norm] at hz hw; exact add_lt_add hz hw
      _ = 2 * Real.pi := by ring
  have him : (z - w).im = 2 * Real.pi * n := by
    rw [hn]; simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]; ring
  have hbound : |2 * Real.pi * (n : ℝ)| ≤ ‖z - w‖ := him ▸ Complex.abs_im_le_norm _
  have hn0 : n = 0 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
    have : |n| < 1 := by exact_mod_cast (by nlinarith [Real.pi_pos] : |(n : ℝ)| < 1)
    have := abs_lt.mp this; omega
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  exact sub_eq_zero.mp hn
theorem IsContLog.hasDerivAt {φ g : ℝ → ℂ} (hg : IsContLog a b φ g)
    {u₀ : ℝ} (hu₀ : u₀ ∈ Set.Ioo a b) {φ' : ℂ} (hφ' : HasDerivAt φ φ' u₀) :
    HasDerivAt g (φ' / φ u₀) u₀ := by
  have hu₀I : u₀ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hu₀
  have hw₀ : φ u₀ ≠ 0 := hg.ne_zero hu₀I
  obtain ⟨r, hr0, hrsp⟩ : ∃ r : ℂ, r ≠ 0 ∧ r * φ u₀ ∈ Complex.slitPlane := by
    rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hw₀ with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  set L : ℝ → ℂ := fun u => Complex.log (r * φ u) - Complex.log r with hL_def
  have hL : HasDerivAt L (φ' / φ u₀) u₀ := by
    have h3 := ((Complex.hasDerivAt_log hrsp).comp u₀ (hφ'.const_mul r)).sub_const (Complex.log r)
    rw [inv_mul_eq_div, mul_div_mul_left _ _ hr0] at h3
    exact h3
  have hLexp : ∀ u, r * φ u ∈ Complex.slitPlane → Complex.exp (L u) = φ u := by
    intro u hu
    rw [hL_def, Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero hu),
      Complex.exp_log hr0, mul_comm, mul_div_assoc, div_self hr0, mul_one]
  have hφc : ContinuousAt φ u₀ := hφ'.continuousAt
  have hIccnhds : Set.Icc a b ∈ 𝓝 u₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu₀) Set.Ioo_subset_Icc_self
  have hgc : ContinuousAt g u₀ := hg.1.continuousAt hIccnhds
  have hsp_nhds : ∀ᶠ u in 𝓝 u₀, r * φ u ∈ Complex.slitPlane :=
    (hφc.const_mul r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hrsp)
  set k₀ : ℂ := g u₀ - L u₀ with hk₀
  have hLkval : L u₀ + k₀ = g u₀ := by rw [hk₀]; ring
  have hLkc : ContinuousAt (fun u => L u + k₀) u₀ := hL.continuousAt.add continuousAt_const
  have hg_ball : ∀ᶠ u in 𝓝 u₀, g u ∈ Metric.ball (g u₀) Real.pi :=
    hgc.eventually_mem (Metric.ball_mem_nhds _ Real.pi_pos)
  have hLk_ball : ∀ᶠ u in 𝓝 u₀, (fun u => L u + k₀) u ∈ Metric.ball (g u₀) Real.pi := by
    apply hLkc.eventually_mem
    apply Metric.isOpen_ball.mem_nhds
    show L u₀ + k₀ ∈ Metric.ball (g u₀) Real.pi
    rw [hLkval]; exact Metric.mem_ball_self Real.pi_pos
  have hg_exp : ∀ᶠ u in 𝓝 u₀, Complex.exp (g u) = φ u := by
    filter_upwards [hIccnhds] with u hu using hg.2 u hu
  have hexpk : Complex.exp k₀ = 1 := by
    rw [hk₀, Complex.exp_sub, hg.2 u₀ hu₀I, hLexp u₀ hrsp, div_self hw₀]
  have hev : g =ᶠ[𝓝 u₀] (fun u => L u + k₀) := by
    filter_upwards [hg_ball, hLk_ball, hg_exp, hsp_nhds] with u hu1 hu2 hu3 hu4
    apply injOn_exp_ball (g u₀) hu1 hu2
    rw [hu3]
    simp only [Complex.exp_add, hLexp u hu4, hexpk, mul_one]
  exact (hL.add_const k₀).congr_of_eventuallyEq hev
theorem argVariation_eq_im_integral (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u => φ' u / φ u) (Set.Icc a b)) :
    argVariation a b φ = (∫ u in a..b, φ' u / φ u).im := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hgderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt g (φ' u / φ u) u :=
    fun u hu => hg.hasDerivAt hu (hderiv u hu)
  have hftc : ∫ u in a..b, φ' u / φ u = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
      (fun u hu => (hgderiv u hu).hasDerivWithinAt) (hint.intervalIntegrable_of_Icc hab)
  rw [argVariation_eq_of_isContLog hab hg, hftc, Complex.sub_im]
noncomputable def lineSeg (z₀ z₁ : ℂ) (u : ℝ) : ℂ := z₀ + (u : ℂ) * (z₁ - z₀)
@[simp] theorem lineSeg_zero (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 0 = z₀ := by simp [lineSeg]
@[simp] theorem lineSeg_one (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 1 = z₁ := by
  simp only [lineSeg, Complex.ofReal_one, one_mul]; ring
theorem lineSeg_re (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).re = z₀.re + u * (z₁.re - z₀.re) := by
  simp [lineSeg, Complex.add_re, Complex.mul_re, Complex.sub_re]
theorem lineSeg_im (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).im = z₀.im + u * (z₁.im - z₀.im) := by
  simp [lineSeg, Complex.add_im, Complex.mul_im, Complex.sub_im]
theorem continuous_lineSeg (z₀ z₁ : ℂ) : Continuous (lineSeg z₀ z₁) := by
  unfold lineSeg; fun_prop
theorem lineSeg_sub_const (z₀ z₁ c : ℂ) :
    (fun u => lineSeg z₀ z₁ u - c) = lineSeg (z₀ - c) (z₁ - c) := by
  funext u; simp only [lineSeg]; ring
end
end CertificatePort29
section CertificatePort30
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex
namespace Complex
theorem arg_add_arg_neg_conj {z : ℂ} (hz : 0 < z.im) :
    z.arg + (-(starRingEnd ℂ z)).arg = Real.pi := by
  have hpi : z.arg ≠ Real.pi := fun h ↦ hz.ne' (Complex.arg_eq_pi_iff.mp h).2
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hz), Complex.arg_conj, if_neg hpi]
  ring
end Complex
variable {a b : ℝ}
theorem argVariation_const (hab : a ≤ b) {c : ℂ} (hc : c ≠ 0) :
    argVariation a b (fun _ ↦ c) = 0 := by
  rw [argVariation_eq_of_isContLog hab
    (g := fun _ ↦ Complex.log c) ⟨continuousOn_const, fun _ _ ↦ Complex.exp_log hc⟩]
  ring
theorem argVariation_lineSeg {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane) :
    argVariation 0 1 (lineSeg z₀ z₁) = z₁.arg - z₀.arg := by
  simpa using
    argVariation_eq_arg_sub_arg zero_le_one (continuous_lineSeg z₀ z₁).continuousOn h
noncomputable def argVariationContourL (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg 2 (2 + Complex.I * T) u)) +
    argVariation 0 1 (fun u ↦ f (lineSeg (2 + Complex.I * T) (1 / 2 + Complex.I * T) u))
noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + Complex.I * (u / 2))) -
    (T / 2) * Real.log Real.pi
noncomputable def argZeta (T : ℝ) : ℝ := (1 / Real.pi) * argVariationContourL riemannZeta T
theorem argVariation_poly_seg {z₀ z₁ : ℂ}
    (hs : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane)
    (hs1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg (z₀ - 1) (z₁ - 1) u ∈ Complex.slitPlane) :
    argVariation 0 1 (fun u ↦ (1 / 2) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
      = (z₁.arg - z₀.arg) + ((z₁ - 1).arg - (z₀ - 1).arg) := by
  have hc2 : (1 / 2 : ℂ) ≠ 0 := one_div_ne_zero two_ne_zero
  have hsub : (fun u ↦ lineSeg z₀ z₁ u - 1) = lineSeg (z₀ - 1) (z₁ - 1) :=
    lineSeg_sub_const z₀ z₁ 1
  have hcont : ContinuousOn (lineSeg z₀ z₁) (Set.Icc (0 : ℝ) 1) :=
    (continuous_lineSeg z₀ z₁).continuousOn
  have hcont1 : ContinuousOn (fun u ↦ lineSeg z₀ z₁ u - 1) (Set.Icc (0 : ℝ) 1) :=
    ((continuous_lineSeg z₀ z₁).sub continuous_const).continuousOn
  have h0 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 :=
    fun u hu ↦ Complex.slitPlane_ne_zero (hs u hu)
  have h1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u - 1 ≠ 0 := fun u hu ↦ by
    rw [congrFun hsub u]; exact Complex.slitPlane_ne_zero (hs1 u hu)
  change argVariation 0 1
    ((fun _ ↦ (1 / 2 : ℂ)) * (lineSeg z₀ z₁ * fun u ↦ lineSeg z₀ z₁ u - 1)) = _
  rw [argVariation_mul zero_le_one continuousOn_const (fun _ _ ↦ hc2) (hcont.mul hcont1)
        (fun u hu ↦ mul_ne_zero (h0 u hu) (h1 u hu)),
    argVariation_const zero_le_one hc2, zero_add,
    argVariation_mul zero_le_one hcont h0 hcont1 h1,
    argVariation_lineSeg hs, hsub, argVariation_lineSeg hs1]
theorem argVariation_poly_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ (1 / 2) * (s * (s - 1))) T = Real.pi := by
  have memRe : ∀ {z₀ z₁ : ℂ} {r : ℝ}, 0 < r → z₀.re = r → z₁.re = r →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hr h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inl <| by
      rw [lineSeg_re, h0, h1]; simpa using hr
  have memIm : ∀ {z₀ z₁ : ℂ} {y : ℝ}, y ≠ 0 → z₀.im = y → z₁.im = y →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hy h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inr <| by
      rw [lineSeg_im, h0, h1]; simpa using hy
  simp only [argVariationContourL]
  rw [argVariation_poly_seg (memRe (r := 2) two_pos (by norm_num) (by simp))
        (memRe (r := 1) one_pos (by norm_num) (by norm_num)),
      argVariation_poly_seg (memIm (y := T) hT.ne' (by simp) (by simp))
        (memIm (y := T) hT.ne' (by simp) (by simp))]
  have hzsub : (1 / 2 + Complex.I * (T : ℂ)) - 1 =
      -(starRingEnd ℂ (1 / 2 + Complex.I * (T : ℂ))) := by
    norm_num [Complex.ext_iff]
  have hz_im : (0 : ℝ) < (1 / 2 + Complex.I * (T : ℂ)).im := by simpa using hT
  rw [hzsub, Complex.ofNat_arg, show (2 : ℂ) - 1 = 1 by norm_num, Complex.arg_one]
  linarith [arg_add_arg_neg_conj hz_im]
end
end CertificatePort30
section CertificatePort31
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Filter Topology Asymptotics
private theorem analyticAt_logDeriv {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) :
    AnalyticAt ℂ (logDeriv f) x :=
  show AnalyticAt ℂ (fun z ↦ deriv f z / f z) x from hf.deriv.div hf h0
private theorem holomorphicOn_logDeriv {f : ℂ → ℂ} {U S : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hSU : S ⊆ U) (h0 : ∀ x ∈ S, f x ≠ 0) : HolomorphicOn (logDeriv f) S := fun x hx ↦
  (analyticAt_logDeriv (hf x (hSU hx)) (h0 x hx)).differentiableAt.differentiableWithinAt
theorem meromorphicOrderAt_eq_residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hf0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      meromorphicOrderAt f z₀ = (n : ℤ) ∧
      AnalyticAt ℂ (logDeriv g) z₀ ∧
      logDeriv f =ᶠ[𝓝[≠] z₀] fun z ↦ (n : ℂ) / (z - z₀) + logDeriv g z := by
  obtain ⟨n, g, hg_an, hg_ne, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hf0
  have hord : meromorphicOrderAt f z₀ = (n : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_natCast.mpr ⟨g, hg_an, hg_ne, hfg⟩]; rfl
  refine ⟨n, g, hg_an, hg_ne, hord, analyticAt_logDeriv hg_an hg_ne, ?_⟩
  have hfg' : f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ n • g z := hfg
  refine ((hfg'.deriv.div hfg').filter_mono nhdsWithin_le_nhds).trans ?_
  filter_upwards [self_mem_nhdsWithin,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz hgz hgan
  have hpow : (z - z₀) ^ n ≠ 0 :=
    pow_ne_zero n (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz))
  have key : deriv (fun w ↦ (w - z₀) ^ n • g w) z / ((z - z₀) ^ n • g z)
      = logDeriv (fun w ↦ (w - z₀) ^ n * g w) z := by simp only [smul_eq_mul, logDeriv_apply]
  have hpow_log := logDeriv_fun_pow (f := fun w : ℂ ↦ w - z₀) (x := z) (by fun_prop) n
  simp only [Pi.div_apply]
  rw [key, logDeriv_mul z hpow hgz (by fun_prop) hgan.differentiableAt, hpow_log, logDeriv_apply]
  simp [div_eq_mul_inv]
theorem finite_rectangle_inter_setOf_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hsub : Rectangle z w ⊆ U)
    (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    (Rectangle z w ∩ {ρ | f ρ = 0}).Finite := by
  have hcompact : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  refine IsCompact.finite ?_ ?_
  ·
    exact hcompact.of_isClosed_subset ((hf.continuousOn.mono hsub).preimage_isClosed_of_isClosed
      (t := {0}) hcompact.isClosed isClosed_singleton) Set.inter_subset_left
  ·
    rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hz₀ hz₀U hU))
      (Set.inter_subset_inter_right _ hsub)
theorem rectangle_mem_nhds_of_not_mem_rectangleBorder {z w ρ : ℂ}
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hρRect : ρ ∈ Rectangle z w) (hρ : ρ ∉ RectangleBorder z w) :
    Rectangle z w ∈ 𝓝 ρ := by
  rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hzw_re,
    Set.uIoo_of_le hzw_im, Set.mem_Ioo, Set.mem_Ioo]
  obtain ⟨hr1, hr2, hi1, hi2⟩ := (mem_Rect hzw_re hzw_im ρ).mp hρRect
  have hreIcc : ρ.re ∈ Set.uIcc z.re w.re := by rw [Set.uIcc_of_le hzw_re]; exact ⟨hr1, hr2⟩
  have himIcc : ρ.im ∈ Set.uIcc z.im w.im := by rw [Set.uIcc_of_le hzw_im]; exact ⟨hi1, hi2⟩
  refine ⟨⟨hr1.lt_of_ne ?_, hr2.lt_of_ne ?_⟩, hi1.lt_of_ne ?_, hi2.lt_of_ne ?_⟩
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨h.symm, himIcc⟩))))
  · exact fun h ↦ hρ (Or.inr (Complex.mem_reProdIm.mpr ⟨h, himIcc⟩))
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr ⟨hreIcc, h.symm⟩))))
  · exact fun h ↦ hρ (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨hreIcc, h⟩)))
theorem rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hss : (Rectangle z w ∩ {ρ | f ρ = 0}).Subsingleton) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  rcases hss.eq_empty_or_singleton with hZ | ⟨ρ, hZ⟩
  ·
    rw [Set.Finite.toFinset_eq_empty.mpr hZ, Finset.sum_empty, mul_zero]
    exact (holomorphicOn_logDeriv hf hsub fun x hx h0 ↦ Set.notMem_empty x
      (hZ ▸ (⟨hx, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))).vanishesOnRectangle (subset_refl _)
  ·
    have hρZ : ρ ∈ Rectangle z w ∩ {ρ | f ρ = 0} := hZ ▸ Set.mem_singleton ρ
    have hρnhds : Rectangle z w ∈ 𝓝 ρ :=
      rectangle_mem_nhds_of_not_mem_rectangleBorder hzw_re hzw_im hρZ.1 fun h ↦ hbd ρ h hρZ.2
    have hfne : ∀ x ∈ Rectangle z w \ {ρ}, f x ≠ 0 := fun x hx h0 ↦
      hx.2 (hZ ▸ (⟨hx.1, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))
    have hne : ¬ ∀ᶠ x in 𝓝 ρ, f x = 0 := fun hev ↦ by
      have h2 : ∀ᶠ x in 𝓝[≠] ρ, f x ≠ 0 := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hρnhds, self_mem_nhdsWithin] with x hx hx'
          using hfne x ⟨hx, hx'⟩
      obtain ⟨x, hx0, hxne⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and h2).exists
      exact hxne hx0
    obtain ⟨n, g, -, -, hord, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv (hf ρ (hsub hρZ.1)) hne
    have near_p : (logDeriv f - fun s ↦ (n : ℂ) / (s - ρ)) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [heq] with x hx; simp only [Pi.sub_apply]; rw [hx]; ring)
        ((Filter.Tendsto.isBigO_one ℂ hlogg.continuousAt).mono nhdsWithin_le_nhds)
    have hres : RectangleIntegral' (logDeriv f) z w = (n : ℂ) :=
      ResidueTheoremOnRectangleWithSimplePole' hzw_re hzw_im hρnhds
        (holomorphicOn_logDeriv hf (Set.sdiff_subset.trans hsub) hfne) near_p
    have htf : hfin.toFinset = {ρ} := by ext x; simp [hZ]
    rw [RectangleIntegral', smul_eq_mul] at hres
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero] at hres
    rw [htf, Finset.sum_singleton, hord, WithTop.untopD_coe]
    push_cast; linear_combination hres
private theorem exists_mem_Ioo_not_mem_finset {S : Finset ℝ} {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) :
    ∃ a : ℝ, min r₁ r₂ < a ∧ a < max r₁ r₂ ∧ a ∉ S := by
  obtain ⟨a, ha, haS⟩ :=
    ((Set.Ioo_infinite (min_lt_max.mpr h)).sdiff S.finite_toSet).nonempty
  exact ⟨a, ha.1, ha.2, by simpa using haS⟩
private theorem ofReal_add_mul_I_re (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
private theorem ofReal_add_mul_I_im (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
private theorem rectangleBorder_vcut {z w : ℂ} {a : ℝ} (hza : z.re ≤ a) (haw : a ≤ w.re) :
    RectangleBorder z (↑a + ↑w.im * I) ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w ∧
      RectangleBorder (↑a + ↑z.im * I) w ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w := by
  have ha : a ∈ Set.uIcc z.re w.re := Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.re ∈ Set.uIcc z.re a → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ha ·) <;>
    have h₂ : ρ.re ∈ Set.uIcc a w.re → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc ha Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto
private theorem rectangleBorder_hcut {z w : ℂ} {b : ℝ} (hzb : z.im ≤ b) (hbw : b ≤ w.im) :
    RectangleBorder z (↑w.re + ↑b * I) ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w ∧
      RectangleBorder (↑z.re + ↑b * I) w ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w := by
  have hb : b ∈ Set.uIcc z.im w.im := Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.im ∈ Set.uIcc z.im b → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc hb ·) <;>
    have h₂ : ρ.im ∈ Set.uIcc b w.im → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc hb Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto
private theorem toFinset_sub_eq_filter {f : ℂ → ℂ} {z w P Q : ℂ}
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hfinP : (Rectangle P Q ∩ {ρ | f ρ = 0}).Finite)
    (hPQ : Rectangle P Q ⊆ Rectangle z w) (p : ℂ → Prop) [DecidablePred p]
    (h : ∀ ρ ∈ Rectangle z w, f ρ = 0 → (ρ ∈ Rectangle P Q ↔ p ρ)) :
    hfinP.toFinset = hfin.toFinset.filter p := by
  ext ρ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hρP, hf0⟩ ↦ ⟨⟨hPQ hρP, hf0⟩, (h ρ (hPQ hρP) hf0).mp hρP⟩,
    fun ⟨⟨hρR, hf0⟩, hp⟩ ↦ ⟨(h ρ hρR hf0).mpr hp, hf0⟩⟩
private theorem rectangleIntegral_logDeriv_subdivide {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    {N : ℕ} {z w Q₁ P₂ ρ₁ ρ₂ : ℂ} {c : ℂ → ℝ} {a : ℝ}
    (ih : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
    (hsub : Rectangle z w ⊆ U) (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hcard : hfin.toFinset.card ≤ N + 1)
    (hρ₁ : ρ₁ ∈ hfin.toFinset) (hρ₂ : ρ₂ ∈ hfin.toFinset)
    (ha1 : min (c ρ₁) (c ρ₂) < a) (ha2 : a < max (c ρ₁) (c ρ₂))
    (hane : ∀ ρ ∈ hfin.toFinset, c ρ ≠ a)
    (hsubR₁R : Rectangle z Q₁ ⊆ Rectangle z w) (hsubR₂R : Rectangle P₂ w ⊆ Rectangle z w)
    (hre1 : z.re ≤ Q₁.re) (him1 : z.im ≤ Q₁.im) (hre2 : P₂.re ≤ w.re) (him2 : P₂.im ≤ w.im)
    (hborder₁ : RectangleBorder z Q₁ ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hborder₂ : RectangleBorder P₂ w ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hmem₁ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle z Q₁ ↔ c ρ ≤ a))
    (hmem₂ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle P₂ w ↔ a ≤ c ρ))
    (hsplit : RectangleIntegral (logDeriv f) z w
        = RectangleIntegral (logDeriv f) z Q₁ + RectangleIntegral (logDeriv f) P₂ w) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  have hcut : ∀ ρ ∈ Rectangle z w, c ρ = a → f ρ ≠ 0 := fun ρ hρ ha hf0 ↦
    hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩) ha
  have hbd₁ : ∀ ρ ∈ RectangleBorder z Q₁, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₁ hρ).elim (hcut ρ (hsubR₁R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hbd₂ : ∀ ρ ∈ RectangleBorder P₂ w, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₂ hρ).elim (hcut ρ (hsubR₂R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hfin₁ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₁R.trans hsub) hz₀U hz₀
  have hfin₂ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₂R.trans hsub) hz₀U hz₀
  have hfeq1 : hfin₁.toFinset = hfin.toFinset.filter (fun ρ ↦ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₁ hsubR₁R _ fun ρ hρ hf0 ↦
      (hmem₁ ρ hρ).trans (hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩)).le_iff_lt
  have hfeq2 : hfin₂.toFinset = hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₂ hsubR₂R _ fun ρ hρ _ ↦ (hmem₂ ρ hρ).trans not_lt.symm
  have hpart : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).card
      + (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).card = hfin.toFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hne1 : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).Nonempty := by
    rcases min_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, hm ▸ ha1⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, hm ▸ ha1⟩⟩
  have hne2 : (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).Nonempty := by
    rcases max_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, not_lt.mpr (hm ▸ ha2).le⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, not_lt.mpr (hm ▸ ha2).le⟩⟩
  have hcard1 : hfin₁.toFinset.card ≤ N := by rw [hfeq1]; have := hne2.card_pos; lia
  have hcard2 : hfin₂.toFinset.card ≤ N := by rw [hfeq2]; have := hne1.card_pos; lia
  rw [hsplit, ih (hsubR₁R.trans hsub) hre1 him1 hbd₁ hfin₁ hcard1,
    ih (hsubR₂R.trans hsub) hre2 him2 hbd₂ hfin₂ hcard2,
    hfeq1, hfeq2, ← mul_add, Finset.sum_filter_add_sum_filter_not]
private theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    ∀ (N : ℕ) {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  have base : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ 1 →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
    fun hsub hre him hbd hfin hcard ↦
      rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton hf hsub hre him hbd hfin
        fun a ha b hb ↦ Finset.card_le_one.mp hcard a (hfin.mem_toFinset.mpr ha) b
          (hfin.mem_toFinset.mpr hb)
  intro N
  induction N with
  | zero =>
    intro z w hsub hre him hbd hfin hcard
    exact base hsub hre him hbd hfin (hcard.trans (Nat.zero_le 1))
  | succ N ih =>
    intro z w hsub hre him hbd hfin hcard
    by_cases hc1 : hfin.toFinset.card ≤ 1
    · exact base hsub hre him hbd hfin hc1
    ·
      obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne⟩ := Finset.one_lt_card_iff.mp (not_le.mp hc1)
      obtain ⟨hz1, hw1, hzi1, hwi1⟩ := (mem_Rect hre him ρ₁).mp (hfin.mem_toFinset.mp hρ₁).1
      obtain ⟨hz2, hw2, hzi2, hwi2⟩ := (mem_Rect hre him ρ₂).mp (hfin.mem_toFinset.mp hρ₂).1
      have hbi : RectangleBorderIntegrable (logDeriv f)
          (↑z.re + ↑z.im * I) (↑w.re + ↑w.im * I) := by
        rw [Complex.re_add_im, Complex.re_add_im]
        exact (holomorphicOn_logDeriv hf
          ((rectangleBorder_subset_rectangle z w).trans hsub) hbd).continuousOn
            |>.rectangleBorder_integrable
      rcases ne_or_eq ρ₁.re ρ₂.re with hred | hreq
      ·
        obtain ⟨a, ha1, ha2, haS⟩ :=
          exists_mem_Ioo_not_mem_finset (S := hfin.toFinset.image Complex.re) hred
        have hza : z.re ≤ a := (lt_of_le_of_lt (le_min hz1 hz2) ha1).le
        have haw : a ≤ w.re := (lt_of_lt_of_le ha2 (max_le hw1 hw2)).le
        have hane : ∀ ρ ∈ hfin.toFinset, ρ.re ≠ a := fun ρ hρ h ↦
          haS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑a + ↑w.im * I : ℂ).re := by simpa using hza
        have him1 : z.im ≤ (↑a + ↑w.im * I : ℂ).im := by simpa using him
        have hre2 : (↑a + ↑z.im * I : ℂ).re ≤ w.re := by simpa using haw
        have him2 : (↑a + ↑z.im * I : ℂ).im ≤ w.im := by simpa using him
        have hsubR₁R : Rectangle z (↑a + ↑w.im * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simpa using haw) le_rfl him1 (by simp)
        have hsubR₂R : Rectangle (↑a + ↑z.im * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simpa using hza) hre2 le_rfl (by simp) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑a + ↑w.im * I) ↔ ρ.re ≤ a) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑a + ↑z.im * I) w ↔ a ≤ ρ.re) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralHSplit' (f := logDeriv f) (a := a)
          (Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.re) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ ha1 ha2 hane hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_vcut hza haw).1 (rectangleBorder_vcut hza haw).2 hmem₁ hmem₂ hsplit
      ·
        obtain ⟨b, hb1, hb2, hbS⟩ := exists_mem_Ioo_not_mem_finset
          (S := hfin.toFinset.image Complex.im) (fun h ↦ hne (Complex.ext hreq h))
        have hzb : z.im ≤ b := (lt_of_le_of_lt (le_min hzi1 hzi2) hb1).le
        have hbw : b ≤ w.im := (lt_of_lt_of_le hb2 (max_le hwi1 hwi2)).le
        have hbne : ∀ ρ ∈ hfin.toFinset, ρ.im ≠ b := fun ρ hρ h ↦
          hbS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑w.re + ↑b * I : ℂ).re := by simpa using hre
        have him1 : z.im ≤ (↑w.re + ↑b * I : ℂ).im := by simpa using hzb
        have hre2 : (↑z.re + ↑b * I : ℂ).re ≤ w.re := by simpa using hre
        have him2 : (↑z.re + ↑b * I : ℂ).im ≤ w.im := by simpa using hbw
        have hsubR₁R : Rectangle z (↑w.re + ↑b * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simp) le_rfl him1 (by simpa using hbw)
        have hsubR₂R : Rectangle (↑z.re + ↑b * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simp) hre2 le_rfl (by simpa using hzb) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑w.re + ↑b * I) ↔ ρ.im ≤ b) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑z.re + ↑b * I) w ↔ b ≤ ρ.im) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralVSplit' (f := logDeriv f) (b := b)
          (Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.im) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ hb1 hb2 hbne hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_hcut hzb hbw).1 (rectangleBorder_hcut hzb hbw).2 hmem₁ hmem₂ hsplit
theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
  rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux hf hU hz₀U hz₀ hfin.toFinset.card hsub hzw_re
    hzw_im hbd hfin le_rfl
theorem re_integral_div_eq_log_norm_sub {a b : ℝ} (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u ↦ φ' u / φ u) (Set.Icc a b)) :
    (∫ u in a..b, φ' u / φ u).re = Real.log ‖φ b‖ - Real.log ‖φ a‖ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
    (fun u hu ↦ (hg.hasDerivAt hu (hderiv u hu)).hasDerivWithinAt)
    (hint.intervalIntegrable_of_Icc hab)
  have hre : ∀ u ∈ Set.Icc a b, (g u).re = Real.log ‖φ u‖ := fun u hu ↦ by
    rw [← hg.2 u hu, Complex.norm_exp, Real.log_exp]
  rw [hftc, Complex.sub_re, hre b (Set.right_mem_Icc.mpr hab), hre a (Set.left_mem_Icc.mpr hab)]
theorem argVariation_lineSeg_eq_im_integral {f : ℂ → ℂ} {P Q : ℂ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℂ f (lineSeg P Q u))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg P Q u) ≠ 0) :
    argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
        = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
      (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
        = Real.log ‖f Q‖ - Real.log ‖f P‖ := by
  have hγderiv : ∀ u : ℝ, HasDerivAt (lineSeg P Q) (Q - P) u := fun u ↦ by
    have h1 : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h := (h1.mul_const (Q - P)).const_add P
    rwa [one_mul] at h
  have hφcont : ContinuousOn (fun u ↦ f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (hf u hu).continuousAt.comp_continuousWithinAt (continuous_lineSeg P Q).continuousWithinAt
  have hderivφ : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u ↦ f (lineSeg P Q u)) (deriv f (lineSeg P Q u) * (Q - P)) u := fun u hu ↦
    ((hf u (Set.Ioo_subset_Icc_self hu)).differentiableAt.hasDerivAt).comp u (hγderiv u)
  have hint : ContinuousOn
      (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (((hf u hu).deriv.continuousAt.comp_continuousWithinAt
        (continuous_lineSeg P Q).continuousWithinAt).mul continuousWithinAt_const).div
      (hφcont u hu) (hne u hu)
  have heqint : (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u))
      = fun u ↦ logDeriv f (lineSeg P Q u) * (Q - P) := by
    funext u; simp only [logDeriv_apply, mul_div_right_comm]
  refine ⟨by rw [argVariation_eq_im_integral zero_le_one hφcont hne hderivφ hint, heqint], ?_⟩
  have h := re_integral_div_eq_log_norm_sub zero_le_one hφcont hne hderivφ hint
  rw [heqint] at h
  rw [h, lineSeg_one, lineSeg_zero]
noncomputable def rectangleArgVariation (f : ℂ → ℂ) (z w : ℂ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u))
private theorem integral_affine_param (F : ℝ → ℂ) (t₁ t₂ : ℝ) :
    ∫ t in t₁..t₂, F t
      = ∫ u in (0 : ℝ)..1, ((t₂ - t₁ : ℝ) : ℂ) * F (t₁ + u * (t₂ - t₁)) := by
  rcases eq_or_ne t₁ t₂ with h | h
  · subst h; simp
  · have hc : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have key : ∫ u in (0 : ℝ)..1, F (t₁ + u * (t₂ - t₁))
        = (t₂ - t₁)⁻¹ • ∫ t in t₁..t₂, F t := by
      have hk := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) F hc t₁
      simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hk
      exact (intervalIntegral.integral_congr (fun u _ ↦ by congr 1; ring)).trans hk
    rw [intervalIntegral.integral_const_mul, key, Complex.real_smul, Complex.ofReal_inv,
      ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]
private theorem hIntegral_eq_lineSeg (g : ℂ → ℂ) (x₁ x₂ y : ℝ) :
    HIntegral g x₁ x₂ y
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u) *
          ((↑x₂ + ↑y * I) - (↑x₁ + ↑y * I)) := by
  rw [HIntegral, integral_affine_param (fun t ↦ g (↑t + ↑y * I)) x₁ x₂]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u = ↑(x₁ + u * (x₂ - x₁)) + ↑y * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg]; push_cast; ring
private theorem vIntegral_eq_lineSeg (g : ℂ → ℂ) (x y₁ y₂ : ℝ) :
    VIntegral g x y₁ y₂
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u) *
          ((↑x + ↑y₂ * I) - (↑x + ↑y₁ * I)) := by
  rw [VIntegral, integral_affine_param (fun t ↦ g (↑x + ↑t * I)) y₁ y₂,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u = ↑x + ↑(y₁ + u * (y₂ - y₁)) * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg, smul_eq_mul]; push_cast; ring
theorem add_mul_sub_mem_uIcc {a b u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.uIcc a b := by
  rw [← segment_eq_uIcc, segment_eq_image' ℝ]
  exact ⟨u, hu, by simp [smul_eq_mul]⟩
private theorem lineSeg_mem_horizontal {a b c : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑b + ↑c * I) u ∈ Set.uIcc a b ×ℂ ({c} : Set ℝ) := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simpa using add_mul_sub_mem_uIcc (a := a) (b := b) hu, by simp⟩
private theorem lineSeg_mem_vertical {a c d : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑a + ↑d * I) u ∈ ({a} : Set ℝ) ×ℂ Set.uIcc c d := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simp, by simpa using add_mul_sub_mem_uIcc (a := c) (b := d) hu⟩
theorem rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation {f : ℂ → ℂ} {U : Set ℂ}
    {z w : ℂ} (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) :
    RectangleIntegral (logDeriv f) z w = I * (rectangleArgVariation f z w : ℂ) := by
  set I0 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u) *
    ((↑w.re + ↑z.im * I) - (↑z.re + ↑z.im * I)) with hI0
  set I1 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u) *
    ((↑w.re + ↑w.im * I) - (↑w.re + ↑z.im * I)) with hI1
  set I2 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u) *
    ((↑z.re + ↑w.im * I) - (↑w.re + ↑w.im * I)) with hI2
  set I3 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u) *
    ((↑z.re + ↑z.im * I) - (↑z.re + ↑w.im * I)) with hI3
  have edge : ∀ {P Q : ℂ},
      (∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg P Q u ∈ RectangleBorder z w) →
      argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
          = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
        (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
          = Real.log ‖f Q‖ - Real.log ‖f P‖ := fun {P Q} hmem ↦
    argVariation_lineSeg_eq_im_integral
      (fun u hu ↦ hf _ (hsub (rectangleBorder_subset_rectangle z w (hmem u hu))))
      (fun u hu ↦ hbd _ (hmem u hu))
  have e0 := edge fun u hu ↦ Or.inl (Or.inl (Or.inl (lineSeg_mem_horizontal hu)))
  have e1 := edge fun u hu ↦ Or.inr (lineSeg_mem_vertical hu)
  have e2 := edge fun u hu ↦
    Or.inl (Or.inr (by rw [Set.uIcc_comm z.re w.re]; exact lineSeg_mem_horizontal hu))
  have e3 := edge fun u hu ↦
    Or.inl (Or.inl (Or.inr (by rw [Set.uIcc_comm z.im w.im]; exact lineSeg_mem_vertical hu)))
  have hsum : RectangleIntegral (logDeriv f) z w = I0 + I1 + I2 + I3 := by
    have h0 : HIntegral (logDeriv f) z.re w.re z.im = I0 := hIntegral_eq_lineSeg _ _ _ _
    have h1 : VIntegral (logDeriv f) w.re z.im w.im = I1 := vIntegral_eq_lineSeg _ _ _ _
    have h2 : HIntegral (logDeriv f) z.re w.re w.im = -I2 := by
      rw [HIntegral_symm, hIntegral_eq_lineSeg]
    have h3 : VIntegral (logDeriv f) z.re z.im w.im = -I3 := by
      rw [VIntegral_symm, vIntegral_eq_lineSeg]
    rw [RectangleIntegral, h0, h1, h2, h3]; ring
  have hre : (I0 + I1 + I2 + I3).re = 0 := by
    rw [hI0, hI1, hI2, hI3]
    simp only [Complex.add_re, e0.2, e1.2, e2.2, e3.2]; ring
  have him : (I0 + I1 + I2 + I3).im = rectangleArgVariation f z w := by
    rw [hI0, hI1, hI2, hI3, rectangleArgVariation, e0.1, e1.1, e2.1, e3.1]
    simp only [Complex.add_im]
  exact hsum.trans (Complex.ext (by rw [hre]; simp) (by rw [him]; simp))
theorem rectangle_zero_count_eq_argVariation {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ)
      = 1 / (2 * Real.pi) * rectangleArgVariation f z w := by
  have h2 := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub hbd
  rw [rectangleIntegral_logDeriv_eq_two_pi_I_sum hf hU hz₀U hz₀ hsub hzw_re hzw_im hbd hfin,
    show (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
      = ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ) by
      push_cast; rfl] at h2
  have h3 : (I : ℂ) * (2 * (Real.pi : ℂ) *
      ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ))
      = I * (rectangleArgVariation f z w : ℂ) := by rw [← h2]; ring
  have h5 : 2 * Real.pi * (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ))
      = rectangleArgVariation f z w := by
    exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero h3
  rw [one_div, inv_mul_eq_div, eq_div_iff (by positivity : (2 * Real.pi) ≠ 0)]
  linear_combination h5
theorem rectangleArgVariation_eq_zero_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ x ∈ U, f x ≠ 0) (hsub : Rectangle z w ⊆ U) :
    rectangleArgVariation f z w = 0 := by
  have heq := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub
    fun ρ hρ ↦ hne ρ (hsub (rectangleBorder_subset_rectangle z w hρ))
  rw [HolomorphicOn.vanishesOnRectangle (holomorphicOn_logDeriv hf (subset_refl U) hne) hsub] at heq
  exact_mod_cast (mul_eq_zero.mp heq.symm).resolve_left Complex.I_ne_zero
end
end CertificatePort31
section CertificatePort32
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open Complex Real
private theorem lineSeg_div (z₀ z₁ c : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ u / c = lineSeg (z₀ / c) (z₁ / c) u := by
  simp only [lineSeg]; ring
private theorem lineSeg_one_sub (z₀ z₁ : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ (1 - u) = lineSeg z₁ z₀ u := by
  simp only [lineSeg]; push_cast; ring
private theorem argVariation_cpow_pi_seg (z₀ z₁ : ℂ) :
    argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      = Real.log π * (-z₁.im / 2) - Real.log π * (-z₀.im / 2) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlog : IsContLog 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      (fun u ↦ (↑(Real.log π) : ℂ) * (-(lineSeg z₀ z₁ u) / 2)) :=
    ⟨(continuous_const.mul ((continuous_lineSeg z₀ z₁).neg.div_const 2)).continuousOn,
      fun u _ ↦ by
        simp only [Complex.cpow_def_of_ne_zero hπ, Complex.ofReal_log Real.pi_pos.le]⟩
  rw [argVariation_eq_of_isContLog zero_le_one hlog]
  simp only [lineSeg_zero, lineSeg_one, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.neg_im, Complex.div_ofNat_im, Complex.neg_re, Complex.div_ofNat_re]
  ring
private theorem argVariationContourL_cpow_pi {T : ℝ} :
    argVariationContourL (fun s ↦ (↑π : ℂ) ^ (-s / 2)) T = -(T / 2) * Real.log π := by
  simp only [argVariationContourL]
  rw [argVariation_cpow_pi_seg 2 (2 + I * ↑T),
    argVariation_cpow_pi_seg (2 + I * ↑T) (1 / 2 + I * ↑T)]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.im_ofNat, Complex.one_im, Complex.div_ofNat_im]
  ring
private theorem continuousOn_Gamma_comp {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (φ u).re) :
    ContinuousOn (fun u ↦ Complex.Gamma (φ u)) (Set.Icc 0 1) := fun u hu ↦
  (Complex.analyticOnNhd_Gamma_re_pos _ (hre u hu)).continuousAt.comp_continuousWithinAt
    hφ.continuousWithinAt
private theorem rectangle_subset_re_pos {T : ℝ} :
    Rectangle (1 / 4 : ℂ) (1 + I * ↑(T / 2)) ⊆ {z : ℂ | 0 < z.re} := fun p hp ↦ by
  rw [Rectangle, Complex.mem_reProdIm] at hp
  rw [show ((1 : ℂ) / 4).re = 1 / 4 by simp, show ((1 : ℂ) + I * ↑(T / 2)).re = 1 by simp,
    Set.uIcc_of_le (by norm_num)] at hp
  exact lt_of_lt_of_le (by norm_num) hp.1.1
private theorem rectangleArgVariation_Gamma {T : ℝ} :
    rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2))
    = argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4) 1 u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u))
    + argVariation 0 1
        (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4) u)) := by
  have hbr : (↑((1 + I * ↑(T / 2) : ℂ)).re + ↑(1 / 4 : ℂ).im * I : ℂ) = 1 := by
    apply Complex.ext <;> simp
  have htl : (↑(1 / 4 : ℂ).re + ↑((1 + I * ↑(T / 2) : ℂ)).im * I : ℂ)
      = 1 / 4 + I * ↑(T / 2) := by
    apply Complex.ext <;> simp
  rw [rectangleArgVariation, Complex.re_add_im, Complex.re_add_im, hbr, htl]
private theorem argVariation_Gamma_bottom :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)) = 0 := by
  have key : ∀ u : ℝ, Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)
      = ↑(Real.Gamma (1 / 4 + u * (3 / 4))) := fun u ↦ by
    rw [show lineSeg (1 / 4 : ℂ) 1 u = ↑((1 / 4 + u * (3 / 4) : ℝ)) by
      simp only [lineSeg]; push_cast; ring, Complex.Gamma_ofReal]
  have hpos : ∀ u ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 / 4 + u * (3 / 4) := fun u hu ↦ by
    nlinarith [hu.1]
  rw [argVariation_eq_arg_sub_arg zero_le_one
      (continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u hu ↦ by
        rw [lineSeg_re, Complex.one_re, Complex.div_ofNat_re, Complex.one_re]
        nlinarith [hu.1])
      (fun u hu ↦ by
        rw [key u, Complex.mem_slitPlane_iff]
        exact Or.inl (by simpa using Real.Gamma_pos_of_pos (hpos u hu))),
    key, key, Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le,
    Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le]
  ring
private theorem lineSeg_vseg_re {T : ℝ} (u : ℝ) :
    (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u).re = 1 / 4 := by
  rw [lineSeg_re]; simp
private theorem continuousOn_Gamma_vseg {T : ℝ} :
    ContinuousOn (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      (Set.Icc 0 1) :=
  continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u _ ↦ by
    rw [lineSeg_vseg_re]; norm_num
private theorem Gamma_vseg_ne_zero {T : ℝ} :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u) ≠ 0 :=
  fun u _ ↦ Gamma_ne_zero_of_re_pos (by rw [lineSeg_vseg_re]; norm_num)
private theorem argVariation_Gamma_left {T : ℝ} :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4 : ℂ) u))
      = -argVariation 0 1
          (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u)) := by
  rw [← argVariation_reverse zero_le_one continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun u ↦ ?_)
  rw [show (0 : ℝ) + 1 - u = 1 - u by ring, lineSeg_one_sub]
private theorem argVariation_Gamma_vseg_reparam {T : ℝ} (hT : 0 < T) :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  have hTc : (↑T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [← argVariation_comp zero_le_one hT.le ((continuous_id.div_const T).continuousOn)
    (fun v hv ↦ ⟨div_nonneg hv.1 hT.le, (div_le_one hT).mpr hv.2⟩) (by simp)
    (by simp [hT.ne']) continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun v ↦ congrArg Complex.Gamma ?_)
  simp only [lineSeg, id_eq]
  push_cast
  field_simp
  ring
private theorem argVariationContourL_Gamma_half {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ Complex.Gamma (s / 2)) T
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  have hrect : rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2)) = 0 :=
    rectangleArgVariation_eq_zero_of_analyticOnNhd Complex.analyticOnNhd_Gamma_re_pos
      (fun _ hx ↦ Gamma_ne_zero_of_re_pos hx) rectangle_subset_re_pos
  rw [rectangleArgVariation_Gamma, argVariation_Gamma_bottom, argVariation_Gamma_left,
    argVariation_Gamma_vseg_reparam hT] at hrect
  have hseg1 : (fun u ↦ Complex.Gamma (lineSeg 2 (2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  have hseg2 : (fun u ↦ Complex.Gamma (lineSeg (2 + I * ↑T) (1 / 2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  simp only [argVariationContourL]
  rw [hseg1, hseg2]
  linarith [hrect]
private theorem argVariation_Gammaℝ_seg (z₀ z₁ : ℂ) (h0 : 0 < z₀.re) (h1 : 0 < z₁.re) :
    argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u / 2).re := fun u hu ↦ by
    rw [Complex.div_ofNat_re, lineSeg_re]
    rcases le_total z₀.re z₁.re with h | h
    · nlinarith [hu.1]
    · nlinarith [hu.2]
  have hfeq : (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        * (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) :=
    funext fun u ↦ Complex.Gammaℝ_def _
  conv_lhs => rw [hfeq]
  exact argVariation_mul zero_le_one
    (((continuous_lineSeg z₀ z₁).neg.div_const 2).const_cpow (Or.inl hπ)).continuousOn
    (fun u _ ↦ by rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _)
    (continuousOn_Gamma_comp ((continuous_lineSeg z₀ z₁).div_const 2) hre)
    (fun u hu ↦ Gamma_ne_zero_of_re_pos (hre u hu))
theorem argVariation_GammaPi_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL Complex.Gammaℝ T = riemannSiegelTheta T := by
  have hpi := argVariationContourL_cpow_pi (T := T)
  have hga := argVariationContourL_Gamma_half hT
  simp only [argVariationContourL] at hpi hga ⊢
  rw [argVariation_Gammaℝ_seg 2 (2 + I * ↑T) (by norm_num) (by simp),
    argVariation_Gammaℝ_seg (2 + I * ↑T) (1 / 2 + I * ↑T) (by simp) (by norm_num),
    riemannSiegelTheta]
  linarith [hpi, hga]
end
end CertificatePort32
section CertificatePort33
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
section
open MeasureTheory Filter Topology
open scoped Nat
namespace Complex
theorem tendsto_natCast_cpow_nhds_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun R : ℕ ↦ (R : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp
    tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [Function.comp_apply, neg_neg]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hR) c).symm
theorem integrableOn_Ioi_bernoulliFun_fract_mul_cpow (p N : ℕ) (hN : 1 ≤ N) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact Complex.integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p (h := fun x : ℝ ↦ x ^ w.re)
    (integrableOn_Ioi_rpow_of_lt hw hN0)
    (Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N) w) fun x hx ↦
      le_of_eq (Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le) w)
noncomputable def eulerMaclaurinRemainderIoi (p : ℕ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi a, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow
    (s : ℂ) (p N : ℕ) (hN : 1 ≤ N) (hsp : 1 < s.re + p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (-s - (p : ℂ)).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith
  have h : IntegrableOn (fun x : ℝ ↦ (-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s *
      ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hw).const_mul _
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.iteratedDeriv_cpow_ofReal_neg s p (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le)]
  ring
end Complex
theorem riemannZeta_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (M N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  have hsne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hsum : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    simpa only [one_div, ← Complex.cpow_neg] using
      (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  have hzeta : ∑' (n : ℕ), (n : ℂ) ^ (-s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.tsum_eq_zero_add,
      Nat.cast_zero, Complex.zero_cpow hs0, zero_add]
    exact tsum_congr fun n ↦ by rw [one_div, ← Complex.cpow_neg]; push_cast; ring_nf
  have hLHS : Tendsto (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) atTop
      (𝓝 ((∑' (n : ℕ), (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s))) := by
    have htsum : Tendsto (fun R : ℕ ↦ ∑ i ∈ Finset.range (R + 1), (i : ℂ) ^ (-s)) atTop
        (𝓝 (∑' (n : ℕ), (n : ℂ) ^ (-s))) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply (htsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [show Finset.Icc N R = Finset.Ico N (R + 1) from by
          ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; lia,
      Finset.sum_Ico_eq_sub _ (by lia : N ≤ R + 1)]
  have hsp : 1 < s.re + ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith
  have hint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun (2 * M + 1) (Int.fract x) : ℂ) *
      iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) :=
    Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s (2 * M + 1) N hN hsp
  have hrem : Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)) atTop
      (𝓝 (Complex.eulerMaclaurinRemainderIoi (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _ hint tendsto_natCast_atTop_atTop).const_mul _
  have h1s : (1 - s).re < 0 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hns : (-s).re < 0 := by rw [Complex.neg_re]; linarith
  have hT1 : Tendsto (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)) atTop
      (𝓝 (((0 : ℂ) - (N : ℂ) ^ (1 - s)) / (1 - s))) :=
    ((Complex.tendsto_natCast_cpow_nhds_zero h1s).sub_const _).div_const _
  have hT2 : Tendsto (fun R : ℕ ↦ ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2) atTop
      (𝓝 (((N : ℂ) ^ (-s) + 0) / 2)) :=
    (Tendsto.const_add _ (Complex.tendsto_natCast_cpow_nhds_zero hns)).div_const _
  have hT3 : Tendsto (fun R : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))) atTop
      (𝓝 (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))) := by
    apply tendsto_finsetSum
    intro k _
    have hek : (-s - ((2 * k - 1 : ℕ) : ℂ)).re < 0 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) (2 * k - 1); linarith
    exact Tendsto.const_mul _ ((Complex.tendsto_natCast_cpow_nhds_zero hek).sub_const _)
  have hRHS := (((hT1.add hT2).sub hT3).add hrem)
  have heq : (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
          + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
          - (∑ k ∈ Finset.Icc 1 M,
              ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                * (ascPochhammer ℂ (2 * k - 1)).eval s
                * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
          + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
              (N : ℝ) (R : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with R hR
    exact Complex.sum_cpow_eq s hsne1 M N R hN hR
  have hkey := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  rw [hzeta] at hkey
  have hconv : ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s) = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp [Complex.zero_cpow hs0]
  have hbern : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
            * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1' : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hsne1
  rw [hconv, hbern, sub_eq_iff_eq_add] at hkey
  rw [hkey]
  field_simp
  ring
end
end CertificatePort33


