-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GammaQuarterLines
-- name    : dusart_psi_433_20261014_GammaQuarterLines
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:22:57.560444+00:00
-- url     : https://prove2.me/theorems/350f94a9-1d47-43bb-bab3-e3dde48cb374
-- title:
--   Dusart smoothing: Gamma Quarter Lines
-- statement:
--   This module gives the complete gamma quarter lines component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_GammaLinear
noncomputable section
namespace DusartSmoothing.RvM
open Complex Real

lemma three_quarters_mem_integerComplement (t : ℝ) :
    (3 / 4 : ℂ) + t * I / 2 ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hh := congrArg Complex.re hn
  norm_num at hh
  have hpos : (0 : ℝ) < n := by linarith
  have hlt : (n : ℝ) < 1 := by linarith
  have hp : (0 : ℤ) < n := by exact_mod_cast hpos
  have hl : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

lemma norm_digamma_three_quarters (t : ℝ) :
    ‖Complex.digamma ((3 / 4 : ℂ) + t * I / 2)‖ ≤ |t| + 4 := by
  let w : ℂ := 3 / 4 + t * I / 2
  have hre : w.re = 3 / 4 := by norm_num [w]
  have him : w.im = t / 2 := by norm_num [w]
  have hn : ‖w‖ ≤ 3 / 4 + |t| / 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hre, him, abs_div] at h
    norm_num [abs_div] at h
    exact h
  have hl : (3 / 4 : ℝ) ≤ ‖w‖ := by simpa only [hre] using Complex.re_le_norm w
  have hden : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hl
  have hi : ‖1 / w‖ ≤ (4 / 3 : ℝ) := by
    rw [norm_div, norm_one]
    apply (div_le_iff₀ hden).2
    linarith
  have h := norm_digamma_linear (by rw [hre]; norm_num) (three_quarters_mem_integerComplement t)
  change ‖Complex.digamma w‖ ≤ |t| + 4
  nlinarith

lemma neg_quarter_not_neg_nat (t : ℝ) :
    ∀ m : ℕ, (-(1 / 4 : ℂ) + t * I / 2) ≠ -(m : ℂ) := by
  intro m h
  have hh := congrArg Complex.re h
  norm_num at hh
  by_cases hm : m = 0
  · subst m; norm_num at hh
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    linarith

lemma norm_digamma_neg_quarter (t : ℝ) :
    ‖Complex.digamma (-(1 / 4 : ℂ) + t * I / 2)‖ ≤ |t| + 8 := by
  let w : ℂ := -(1 / 4) + t * I / 2
  have hre : w.re = -(1 / 4 : ℝ) := by norm_num [w]
  have hl : (1 / 4 : ℝ) ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    rw [hre] at h
    norm_num at h
    exact h
  have hden : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hl
  have hi : ‖w⁻¹‖ ≤ (4 : ℝ) := by
    rw [norm_inv]
    apply (inv_le_comm₀ hden (by norm_num)).2
    norm_num
    exact hl
  have hrec := Complex.digamma_apply_add_one w (neg_quarter_not_neg_nat t)
  have he : w + 1 = (3 / 4 : ℂ) + t * I / 2 := by dsimp [w]; ring
  rw [he] at hrec
  have hψ : Complex.digamma w = Complex.digamma ((3 / 4 : ℂ) + t * I / 2) - w⁻¹ := by
    linear_combination -hrec
  change ‖Complex.digamma w‖ ≤ |t| + 8
  rw [hψ]
  exact (norm_sub_le _ _).trans (by linarith [norm_digamma_three_quarters t])

end DusartSmoothing.RvM


