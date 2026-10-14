-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZetaGrowth
-- name    : dusart_psi_433_20261014_ZetaGrowth
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:38.111273+00:00
-- url     : https://prove2.me/theorems/e692681a-5657-44f3-a648-807defaa43ca
-- title:
--   Dusart smoothing: Zeta Growth
-- statement:
--   This module gives the complete zeta growth component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

/- Adapted from accepted proofs de06bf5a-4f90-4eba-a811-ca02ab3e189d
and e8423ab6-3e6e-422a-9137-beaa4d76bbc7.
Copyright (c) 2026 Anthropic, PBC. Apache-2.0. -/
import Definitions.Def_dusart_psi_433_20261014_ZetaEMIdentity
import Definitions.Def_dusart_psi_433_20261014_ZetaEMBound
import Definitions.Def_dusart_psi_433_20261014_JensenCount
open Complex Set MeasureTheory Real
noncomputable section
namespace DusartSmoothing.RvM
open DusartSmoothing.ZetaEM

lemma norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := zeta0_integral_bound 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← zeta0_eq_zeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring

lemma zeta_growth_right_at (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have hσpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  have h := norm_riemannZeta_le_of_re_pos hσpos hs1
  have h1' : 1 / ‖1 - s‖ ≤ 1 := by
    rw [norm_sub_rev] at h1
    rw [div_le_one (by linarith)]
    exact h1
  have hσ' : (3 : ℝ) / 20 ≤ s.re := by
    have := hσ; norm_num at this ⊢; linarith
  have h2 : ‖s‖ / s.re ≤ 1 + 20 / 3 * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / (3 / 20) := by gcongr
      _ = 1 + 20 / 3 * |s.im| := by ring
  have ht : 0 ≤ |s.im| := abs_nonneg _
  linarith [h, h1', h2, ht]


lemma actual_reZeroSet_card_bound (T : ℝ) (hT : 4 ≤ T) :
    (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤
      9 * Real.log (T + 5) + 27 := by
  exact reZeroSet_card_le_linear_growth
    (by simpa only [Real.rpow_one] using zeta_growth_right_at) T hT

lemma actual_backlund_horizontal_numerical_bound (T : ℝ) (hT : 4 ≤ T)
    (hnz : ∀ σ ∈ Set.Icc (1/2:ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤
      Real.pi * (9 * Real.log (T+5) + 28) := by
  exact backlund_horizontal_numerical_bound
    (by simpa only [Real.rpow_one] using zeta_growth_right_at) T hT hnz

end DusartSmoothing.RvM


