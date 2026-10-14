-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GoodHeightsRight
-- name    : dusart_psi_433_20261014_GoodHeightsRight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:41:15.544772+00:00
-- url     : https://prove2.me/theorems/5b823518-caaa-4d50-839d-a7eb93d6714e
-- title:
--   Dusart smoothing: Good Heights Right
-- statement:
--   This module gives the complete good heights right component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GoodHeightGap
import Definitions.Def_dusart_psi_433_20261014_ZetaPartialFractions
import Definitions.Def_dusart_psi_433_20261014_PerronAnalytic
noncomputable section
namespace DusartSmoothing
open Complex Real Set Metric Filter Topology

lemma zeta_nonzero_of_goodHeight {T : ℝ} (hT : RvM.GoodHeight T)
    {s : ℂ} (hs : -(1 / 2 : ℝ) ≤ s.re) (hi : s.im = T) : riemannZeta s ≠ 0 := by
  intro hz
  exact hT s ((zeta_zero_iff_nontrivial_in_half_strip s hs).1 hz) hi

lemma good_heights_right : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 7 ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧ RvM.GoodHeight R ∧
      ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2,
        ‖logDeriv riemannZeta (σ + R * I)‖ ≤
          C * ((j : ℝ) + 3)^2 * Real.log ((j : ℝ) + 4) := by
  classical
  obtain ⟨C, hC, hpf⟩ := Landau.zeta_logDeriv_partial_fraction
  refine ⟨35 * C, by positivity, fun j hj => ?_⟩
  have hjR : (7 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨R, hR1, hR2, hgood, hgap⟩ := good_height_with_global_gap j hj
  have hRp : 0 < R := by linarith
  obtain ⟨Z, hZ, hcount, hfrac⟩ := hpf R (by rw [abs_of_pos hRp]; linarith)
  let B : ℝ := 2 * (16 * ((j : ℝ) + 3)^2 + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Real.log (|R| + 3) ≤ Real.log ((j : ℝ) + 4) := by
    rw [abs_of_pos hRp]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log ((j : ℝ) + 4) := Real.log_nonneg (by linarith)
  have hZinfo : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧
      ρ.im ≤ (j : ℝ) + 3 := by
    intro ρ hρ
    have hm : ρ ∈ {ρ ∈ Metric.closedBall (2 + R * I) (22/25 * (91/50)) |
        riemannZeta ρ = 0} := by rw [← hZ]; exact hρ
    obtain ⟨hball, hz⟩ := hm
    have hn : ‖ρ - ((2 : ℂ) + R * I)‖ ≤ (22 / 25 : ℝ) * (91 / 50) := by
      simpa only [Metric.mem_closedBall, Complex.dist_eq] using hball
    have hr := (Complex.abs_re_le_norm (ρ - ((2 : ℂ) + R * I))).trans hn
    have hi := (Complex.abs_im_le_norm (ρ - ((2 : ℂ) + R * I))).trans hn
    norm_num only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, mul_one, zero_add, add_zero] at hr hi
    obtain ⟨hrlo, _⟩ := abs_le.mp hr
    obtain ⟨hilo, hiup⟩ := abs_le.mp hi
    have hp : 0 < ρ.re := by linarith
    have hlt : ρ.re < 1 := by
      by_contra hh
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hh) hz
    exact ⟨⟨hz, hp, hlt⟩, by linarith, by linarith⟩
  refine ⟨R, hR1, hR2, hgood, ?_⟩
  intro σ hσ
  let s : ℂ := σ + R * I
  have hs : s ∈ Metric.closedBall (2 + R * I) (3 / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have he : s - ((2 : ℂ) + R * I) = ((σ - 2 : ℝ) : ℂ) := by dsimp [s]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hσ.2])]
    linarith [hσ.1]
  have hz : riemannZeta s ≠ 0 := zeta_nonzero_of_goodHeight hgood
    (by norm_num [s]; linarith [hσ.1]) (by simp [s])
  have hterm : ∀ ρ ∈ Z,
      ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
        B * (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    intro ρ hρ
    obtain ⟨hnt, hpos, hup⟩ := hZinfo ρ hρ
    have hg := hgap ρ hnt hpos hup
    change 1 / B ≤ |R - ρ.im| at hg
    have hn : 1 / B ≤ ‖s - ρ‖ := hg.trans (by simpa [s] using Complex.abs_im_le_norm (s - ρ))
    have hdn : 0 < ‖s - ρ‖ := (one_div_pos.mpr hB).trans_le hn
    have hm : 1 ≤ B * ‖s - ρ‖ := by
      simpa only [mul_comm] using (div_le_iff₀ hB).1 hn
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hdn).2
    have hmul := mul_le_mul_of_nonneg_left hm
      (Nat.cast_nonneg (analyticOrderNatAt riemannZeta ρ) : (0 : ℝ) ≤ _)
    nlinarith
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      B * ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    calc _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, B * (analyticOrderNatAt riemannZeta ρ : ℝ) := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.mul_sum]
  have hmain := norm_le_norm_sub_add (logDeriv riemannZeta s)
    (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ))
  have hfrac1 := hfrac s hs hz
  have hc : ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      C * Real.log ((j : ℝ) + 4) := hcount.trans (mul_le_mul_of_nonneg_left hlog hC.le)
  have hf : ‖logDeriv riemannZeta s -
      ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log ((j : ℝ) + 4) := hfrac1.trans (mul_le_mul_of_nonneg_left hlog hC.le)
  have hb : B + 1 ≤ 35 * ((j : ℝ) + 3)^2 := by dsimp [B]; nlinarith
  have hsum1 := hsum.trans (mul_le_mul_of_nonneg_left hc hB.le)
  have hlast := mul_le_mul_of_nonneg_right hb (mul_nonneg hC.le hlog0)
  change ‖logDeriv riemannZeta s‖ ≤ _
  nlinarith

end DusartSmoothing


