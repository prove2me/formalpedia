-- Prove2me | Definitions.Def_dusart_psi_433_20261014_HorizontalBounds
-- name    : dusart_psi_433_20261014_HorizontalBounds
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:53:32.909978+00:00
-- url     : https://prove2.me/theorems/a0264dde-c781-469b-b0a4-ff3247be2b71
-- title:
--   Dusart smoothing: Horizontal Bounds
-- statement:
--   This module gives the complete horizontal bounds component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GoodHeights
import Definitions.Def_dusart_psi_433_20261014_PerronLeftLine
noncomputable section
namespace DusartSmoothing
open Complex Real Set Metric Filter Topology MeasureTheory

lemma norm_quadraticKernel_le_height (x : ℝ) (hx : 0 < x) {s : ℂ}
    (hi : 0 < |s.im|) :
    ‖quadraticKernel x s‖ ≤ x ^ (s.re + 2) / |s.im| ^ 3 := by
  have h0 := Complex.abs_im_le_norm s
  have h1 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have h2 : |s.im| ≤ ‖s + 2‖ := by simpa using Complex.abs_im_le_norm (s + 2)
  have hd : |s.im|^3 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by
    calc |s.im|^3 = |s.im| * |s.im| * |s.im| := by ring
      _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by gcongr
  rw [quadraticKernel, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  norm_num only [Complex.add_re, Complex.re_ofNat]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) hd

lemma norm_perron_horizontal_point (x : ℝ) (hx : 1 ≤ x) (C k R : ℝ)
    (hC : 0 < C) (hk : 7 ≤ k) (hR : k ≤ R) {s : ℂ}
    (hsi : |s.im| = R) (hs : s.re ≤ 2)
    (hZ : ‖logDeriv riemannZeta s‖ ≤ C * (k + 3)^2 * Real.log (k + 4)) :
    ‖perronIntegrand x s‖ ≤ 8 * C * x^4 * Real.log (k + 4) / (k + 4) := by
  have hxp : 0 < x := by linarith
  have hkp : 0 < k := by linarith
  have hRp : 0 < R := hkp.trans_le hR
  have hlog : 0 ≤ Real.log (k + 4) := Real.log_nonneg (by linarith)
  have hK := norm_quadraticKernel_le_height x hxp (s := s) (by rw [hsi]; exact hRp)
  rw [hsi] at hK
  have hpow : x ^ (s.re + 2) ≤ x^4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by linarith : s.re + 2 ≤ (4 : ℝ))
  have hK1 : ‖quadraticKernel x s‖ ≤ x^4 / k^3 := hK.trans
    (div_le_div₀ (by positivity) hpow (by positivity) (by gcongr))
  have hsq : (k + 3)^2 ≤ 4 * k^2 := by nlinarith
  have hZ1 : ‖logDeriv riemannZeta s‖ ≤ 4 * C * k^2 * Real.log (k + 4) := by
    calc _ ≤ C * (k + 3)^2 * Real.log (k + 4) := hZ
      _ ≤ C * (4 * k^2) * Real.log (k + 4) := by gcongr
      _ = _ := by ring
  rw [perronIntegrand, norm_mul, norm_neg]
  calc
    ‖quadraticKernel x s‖ * ‖logDeriv riemannZeta s‖
      ≤ (x^4 / k^3) * (4 * C * k^2 * Real.log (k + 4)) := by gcongr
    _ = 4 * C * x^4 * Real.log (k + 4) / k := by field_simp <;> ring
    _ ≤ 8 * C * x^4 * Real.log (k + 4) / (k + 4) := by
      apply (div_le_div_iff₀ hkp (by linarith : 0 < k + 4)).2
      have hn := mul_nonneg (by positivity : 0 ≤ 4 * C * x^4 * Real.log (k + 4))
        (by linarith : 0 ≤ k - 4)
      nlinarith

lemma norm_perron_horizontal_integral (x : ℝ) (hx : 1 ≤ x) (C k R : ℝ)
    (hC : 0 < C) (hk : 7 ≤ k) (hR : k ≤ R) (t : ℝ) (ht : |t| = R)
    (hZ : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) 2,
      ‖logDeriv riemannZeta (σ + t * I)‖ ≤ C * (k + 3)^2 * Real.log (k + 4)) :
    ‖∫ σ in (-(1 / 2) : ℝ)..2, perronIntegrand x (σ + t * I)‖ ≤
      20 * C * x^4 * Real.log (k + 4) / (k + 4) := by
  have hb : ∀ σ ∈ Set.uIoc (-(1 / 2) : ℝ) 2,
      ‖perronIntegrand x (σ + t * I)‖ ≤ 8 * C * x^4 * Real.log (k + 4) / (k + 4) := by
    intro σ hσ
    have hσ1 : -(1 / 2 : ℝ) ≤ σ ∧ σ ≤ 2 := by
      rw [Set.uIoc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 2)] at hσ
      exact ⟨hσ.1.le, hσ.2⟩
    exact norm_perron_horizontal_point x hx C k R hC hk hR
      (by simpa using ht) (by simpa using hσ1.2) (hZ σ hσ1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  norm_num at h
  exact h.trans_eq (by ring)

lemma log_div_height_tendsto :
    Tendsto (fun j : ℕ => Real.log ((j : ℝ) + 11) / ((j : ℝ) + 11)) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h.comp (tendsto_atTop_add_const_right atTop 11 tendsto_natCast_atTop_atTop)

end DusartSmoothing


