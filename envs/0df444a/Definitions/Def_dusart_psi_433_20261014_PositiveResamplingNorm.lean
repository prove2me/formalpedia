-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PositiveResamplingNorm
-- name    : dusart_psi_433_20261014_PositiveResamplingNorm
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T12:12:16.304015+00:00
-- url     : https://prove2.me/theorems/d452425b-2ebc-471b-a8b5-686ebe36799a
-- title:
--   Dusart smoothing: Positive Resampling Norm
-- statement:
--   This module gives the complete positive resampling norm component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WindowPowers
import Definitions.Def_dusart_psi_433_20261014_ResamplingCoefficients
noncomputable section
namespace DusartSmoothing
open Real Complex

lemma finite_positive_resampling_norm_bound (R x ν a : ℝ) (hR : 0 < R) (hx : 1 < x)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hX : max (836 / 100 : ℝ) (8 / R) < X R x)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed (X R x) ≤ ν)
    (hk : k (X R x) ν = 1) (ha : 0 < a)
    (hab : a + 2 * (optimalWidth (X R x) ν * x) ≤ x * (1 + 2 * optimalWidth (X R x) ν))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) ≤
      x * (1 + 2 * optimalWidth (X R x) ν)^3 * optimalWidth (X R x) ν / 2 := by
  classical
  have hXp := (threshold_facts R x hR hX).1
  have hδ := optimalWidth_pos (X R x) ν hXp hν
  have hxp : 0 < x := by linarith
  have hC : 0 < x * (1 + 2 * optimalWidth (X R x) ν)^3 := by positivity
  rcases Z.eq_empty_or_nonempty with he | hn
  · rw [he]; simp only [Finset.sum_empty]; positivity
  · let B : ℝ := max (transformHeight (X R x) ν) (Z.sup' hn Complex.im)
    let W := (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset
    have hsub : Z ⊆ W := by
      intro ρ hρ
      rw [Set.Finite.mem_toFinset]
      have hh := RvM.nontrivial_zero_abs_height ρ (hZ ρ hρ).1
      rw [abs_of_pos (hZ ρ hρ).2] at hh
      exact ⟨(hZ ρ hρ).1, by linarith [Real.pi_gt_three],
        (Finset.le_sup' Complex.im hρ).trans (le_max_right _ _)⟩
    let p : ℂ → ℝ := fun ρ => (RvM.zeroMult ρ : ℝ) *
      resamplingZeroWeight (optimalWidth (X R x) ν) (transformHeight (X R x) ν) ρ.im * (‖(x : ℂ)^ρ‖ / x)
    have hs : (∑ ρ ∈ Z, p ρ) ≤ ∑ ρ ∈ W, p ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro ρ hρ _
      have hh : 0 < ρ.im := by rw [Set.Finite.mem_toFinset] at hρ; linarith [hρ.2.1]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (resamplingZeroWeight_nonneg _ _ _ hh))
        (div_nonneg (norm_nonneg _) hxp.le)
    have hw := positive_window_power_weight_bound R x ν B hR hx hzero hX hν hν1 hseed hk (le_max_left _ _)
    change 2 * (∑ ρ ∈ W, p ρ) < optimalWidth (X R x) ν at hw
    have hpower : 2 * (∑ ρ ∈ Z, p ρ) ≤ optimalWidth (X R x) ν := by linarith
    have hnorm : (∑ ρ ∈ Z, ‖(RvM.zeroMult ρ : ℂ) * smoothedZeroKernel a (optimalWidth (X R x) ν * x) ρ‖) ≤
        x * (1 + 2 * optimalWidth (X R x) ν)^3 * ∑ ρ ∈ Z, p ρ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul, Complex.norm_natCast]
      have hc := mul_le_mul_of_nonneg_left
        (norm_smoothed_kernel_resampling_bound x (optimalWidth (X R x) ν) a
          (transformHeight (X R x) ν) hxp hδ ha hab ρ (hZ ρ hρ).1 (hZ ρ hρ).2)
        (Nat.cast_nonneg (RvM.zeroMult ρ) : (0 : ℝ) ≤ RvM.zeroMult ρ)
      apply hc.trans_eq
      dsimp [p]
      field_simp [hxp.ne']
      <;> ring
    have hm := mul_le_mul_of_nonneg_left hpower hC.le
    linarith

end DusartSmoothing


