-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaPartialFractions
-- name    : dusart_psi_433_20261014_ZetaPartialFractions
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:24:53.708413+00:00
-- url     : https://prove2.me/theorems/5c38b94c-d0bc-480f-a1ab-8c3f34ab875b
-- title:
--   Dusart smoothing: Zeta Partial Fractions
-- statement:
--   This module gives the complete zeta partial fractions component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LandauDisk
import Definitions.Def_dusart_psi_433_20261014_ZetaGrowth
/- Copyright (c) 2026 Anthropic PBC; Apache-2.0. -/
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real Set Metric Filter Topology

theorem analyticOnNhd_riemannZeta_landau {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)


lemma zeta_growth_quarter :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  refine ⟨1, 80 / 3, by norm_num, fun s hσ _ ht => ?_⟩
  have hn : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    exact ht.trans h
  have h := zeta_growth_right_at s (by linarith) hn
  rw [Real.rpow_one] at h ⊢
  linarith

/-- Lower bound at the Jensen disc centre: 0 < 2 − π²/6 ≤ ‖ζ(s)‖ for Re s ≥ 2. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith


/-- 1/3 < 2 − π²/6 (π < 3.15 ⇒ π²/6 < 1.654). -/
lemma one_third_lt_two_sub_pi_sq_div_six_landau : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Consumer interface.** ‖ζ(2 + it)‖ ≥ 1/3 for all real t. -/
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six_landau]


/-- Upper bound on Re s ≥ 2: ‖ζ(s)‖ ≤ π²/6. -/
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith


end DusartSmoothing.RvM
namespace DusartSmoothing.Landau
open Complex Real Set Metric Filter Topology

theorem zeta_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  obtain ⟨A, C₀, hC₀, hgrow⟩ := DusartSmoothing.RvM.zeta_growth_quarter
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hCpos : (0:ℝ) < (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) := by
    have h1 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨(44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1), hCpos,
    fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hζs₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)
  have hlow : (1/3 : ℝ) ≤ ‖riemannZeta s₀‖ := DusartSmoothing.RvM.zeta_lower_bound_two t
  -- analyticity on the closed ball of radius 91/50
  have hone : (1 : ℂ) ∉ Metric.closedBall s₀ (91/50) := by
    intro h
    rw [Metric.mem_closedBall, Complex.dist_eq] at h
    have him : ((1 : ℂ) - s₀).im = -t := by simp [hs₀]
    have : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
      calc |t| = |((1:ℂ) - s₀).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - s₀‖ := Complex.abs_im_le_norm _
    linarith
  have hfa : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    DusartSmoothing.RvM.analyticOnNhd_riemannZeta_landau hone
  -- the B-bound on the (24/25)·(91/50)-ball
  set B : ℝ := 3 * (C₀ * (|t| + 2) ^ A' + 2) with hB
  have ht2 : (1:ℝ) ≤ |t| + 2 := by linarith
  have hpow1 : (1:ℝ) ≤ (|t| + 2) ^ A' := Real.one_le_rpow ht2 hA'0
  have hB2 : 2 ≤ B := by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)), ‖riemannZeta w‖ ≤ B * ‖riemannZeta s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : |w.re - 2| ≤ 24/25 * (91/50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this
      linarith
    have hwim : |w.im - t| ≤ 24/25 * (91/50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this
      linarith
    have hwim1 : 1 ≤ |w.im| := by
      have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith [hwim]
    have hwimt : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h2 : |w.im| - |t| ≤ |w.im - t| := this
      linarith [hwim]
    have hbound : ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
      rcases le_or_gt w.re 2 with hre2 | hre2
      · have h14 : (1/4 : ℝ) ≤ w.re := by
          rw [abs_le] at hwre
          linarith
        have := hgrow w h14 hre2 hwim1
        calc ‖riemannZeta w‖ ≤ C₀ * |w.im| ^ A := this
          _ ≤ C₀ * (|t| + 2) ^ A' := by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^ A ≤ |w.im| ^ A' :=
                    Real.rpow_le_rpow_of_exponent_le hwim1 (le_max_left _ _)
                _ ≤ (|t| + 2) ^ A' := Real.rpow_le_rpow (by linarith) hwimt hA'0
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by linarith
      · have := DusartSmoothing.RvM.norm_riemannZeta_le_of_two_le_re (s := w) (by linarith)
        have hπ : (Real.pi : ℝ) ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤ Real.pi ^ 2 / 6 := this
          _ ≤ 2 := hπ
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
    calc ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := hbound
      _ = (B * (1/3)) := by rw [hB]; ring
      _ ≤ B * ‖riemannZeta s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := logDeriv_partial_fraction_disk (f := riemannZeta)
    (by norm_num : (0:ℝ) < 91/50) hfa hζs₀ hB2 hfB
  -- logarithmic bookkeeping shared by the count bound and the partial-fraction bound
  have hT3 : (2:ℝ) ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 9 := by norm_num
      _ ≤ |t| + 3 := by linarith
  have hlogB : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
    have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
      rw [hB]
      nlinarith [hpow1, hC₀]
    have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
      Real.log_le_log (by rw [hB]; positivity) h1
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
    have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
      rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
    rw [hBeq]
    nlinarith [mul_nonneg hA'0 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
      mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), hT3]
  have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [hZset]
  · refine hZcount.trans ?_
    have hratio : ((24/25 : ℝ))/(22/25) = 12/11 := by norm_num
    have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlogpos : (0:ℝ) < Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]
          linarith
      _ ≤ 12 * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 44795000 * 50 / 91 * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]
  · intro s hs hζs
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hζs).trans ?_
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]

end DusartSmoothing.Landau


