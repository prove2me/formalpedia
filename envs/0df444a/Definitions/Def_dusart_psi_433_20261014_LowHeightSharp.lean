-- Prove2me | Definitions.Def_dusart_psi_433_20261014_LowHeightSharp
-- name    : dusart_psi_433_20261014_LowHeightSharp
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:25:49.861374+00:00
-- url     : https://prove2.me/theorems/73d8a3dc-869b-4545-954f-bd289b236a89
-- title:
--   Dusart smoothing: Low Height Sharp
-- statement:
--   This module gives the complete low height sharp component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ThetaIntegral
noncomputable section
namespace DusartSmoothing.LowHeight
open Complex Real Set MeasureTheory

lemma upper_integrand_sharp (z : ℂ) (hz : z.re ≤ 1 / 2) (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)‖ ≤
      (2001 / 1000 : ℝ) * thetaTail x := by
  have hx0 : 0 < x := by linarith
  have hk := theta_kernel_sharp x hx.le
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hp : x ^ (z - 1).re ≤ x ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by simp; linarith)
  have he : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow, one_div]
  have hn : ‖(HurwitzZeta.evenKernel 0 x : ℂ) - 1‖ =
      HurwitzZeta.evenKernel 0 x - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hk.1]
  rw [he] at hp
  rw [hn]
  calc x ^ (z - 1).re * (HurwitzZeta.evenKernel 0 x - 1)
      ≤ (1 / Real.sqrt x) * ((2001 / 1000 : ℝ) * Real.exp (-Real.pi * x)) :=
        mul_le_mul hp hk.2 hk.1 (by positivity)
    _ = _ := by dsimp [thetaTail]; ring

lemma exp_neg_pi_lt : Real.exp (-Real.pi) < (217 / 5000 : ℝ) := by
  have he : (5000 / 217 : ℝ) < Real.exp (157 / 50 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 157 / 50) 11
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hπ : (157 / 50 : ℝ) < Real.pi := by have h := Real.pi_gt_d2; norm_num at h; exact h
  have hh : (5000 / 217 : ℝ) < Real.exp Real.pi := he.trans (Real.exp_lt_exp.mpr hπ)
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos Real.pi)).2
  linarith

lemma upper_mellin_sharp (z : ℂ) (hz : z.re ≤ 1 / 2) :
    ‖mellin upperKernel z‖ < (1 / 40 : ℝ) := by
  have hd := thetaTail_integrable.const_mul (2001 / 1000 : ℝ)
  have hle := norm_integral_le_of_norm_le hd
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => upper_integrand_sharp z hz x hx)
  have hrepr : mellin upperKernel z =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1) := by
    unfold mellin upperKernel
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioi]
    rw [inter_eq_right.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 by intro x hx; exact lt_trans zero_lt_one (show (1 : ℝ) < x from hx))]
  rw [hrepr] at *
  rw [integral_const_mul] at hle
  have hm := mul_le_mul_of_nonneg_left thetaTail_integral_bound
    (by norm_num : (0 : ℝ) ≤ 2001 / 1000)
  apply lt_of_le_of_lt (hle.trans hm)
  have hden : 0 < Real.pi + 3 / 8 := by positivity
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hden).2
  have hπ : (157 / 50 : ℝ) < Real.pi := by have h := Real.pi_gt_d2; norm_num at h; exact h
  nlinarith [exp_neg_pi_lt]

lemma completed_entire_sharp (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ < (1 / 40 : ℝ) := by
  rw [completed_mellin_split s hσ1, norm_div]
  have h1 := upper_mellin_sharp (s / 2) (by simp; linarith)
  have h2 := upper_mellin_sharp ((1 - s) / 2) (by simp; linarith)
  have hn := norm_add_le (mellin upperKernel (s / 2)) (mellin upperKernel ((1 - s) / 2))
  norm_num
  linarith

end DusartSmoothing.LowHeight


