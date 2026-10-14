-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GaussianWindow
-- name    : dusart_psi_433_20261014_GaussianWindow
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:46:57.420519+00:00
-- url     : https://prove2.me/theorems/fce2da03-9434-4714-bc17-147c91845868
-- title:
--   Dusart smoothing: Gaussian Window
-- statement:
--   This module gives the complete gaussian window component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ResamplingWeights
import Definitions.Def_dusart_psi_433_20261014_CountAbsorption
import Definitions.Def_dusart_psi_433_20261014_ReflectionAbsorption
noncomputable section
namespace DusartSmoothing
open Real Complex

lemma gaussian_window_weight_bound (X ν B : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed X ≤ ν)
    (hk : k X ν = 1) (hB : transformHeight X ν ≤ B) :
    (∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im *
        Real.exp (-X^2 / Real.log ρ.im)) <
      optimalWidth X ν - (2 / 100 : ℝ) * (optimalWidth X ν * ν / (X + 2 * ν)) := by
  classical
  let Z := (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset
  let L := (RvM.finite_zero_window (b := transformHeight X ν) (by norm_num : (0 : ℝ) < 4)).toFinset
  let H := (RvM.finite_zero_window (a := transformHeight X ν) (b := B) (transformHeight_pos X ν)).toFinset
  have hT4 : 4 < transformHeight X ν := by
    linarith [transformHeight_gt_five_hundred X ν hX hν]
  have heL : Z.filter (fun ρ => ρ.im ≤ transformHeight X ν) = L := by
    ext ρ
    simp only [Z, L, Finset.mem_filter, Set.Finite.mem_toFinset, RvM.zerosIn]
    constructor
    · intro h; exact ⟨h.1.1, h.1.2.1, h.2⟩
    · intro h; exact ⟨⟨h.1, h.2.1, h.2.2.trans hB⟩, h.2.2⟩
  have heH : Z.filter (fun ρ => ¬ρ.im ≤ transformHeight X ν) = H := by
    ext ρ
    simp only [Z, H, Finset.mem_filter, Set.Finite.mem_toFinset, RvM.zerosIn]
    constructor
    · intro h; exact ⟨h.1.1, lt_of_not_ge h.2, h.1.2.2⟩
    · intro h; exact ⟨⟨h.1, hT4.trans h.2.1, h.2.2⟩, not_le.mpr h.2.1⟩
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im *
      Real.exp (-X^2 / Real.log ρ.im)) =
      (∑ ρ ∈ L, (RvM.zeroMult ρ : ℝ) * gaussianZeroWeight X ρ.im) +
      4 / optimalWidth X ν^2 * ∑ ρ ∈ H, (RvM.zeroMult ρ : ℝ) * gaussianTailZeroWeight X ρ.im := by
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.im ≤ transformHeight X ν), heL, heH]
    congr 1
    · apply Finset.sum_congr rfl
      intro ρ hρ
      have hz : ρ ∈ RvM.zerosIn 4 (transformHeight X ν) := by
        simpa only [L, Set.Finite.mem_toFinset] using hρ
      have hh := hz.2.2
      rw [resamplingZeroWeight, if_pos hh, gaussianZeroWeight]
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hz : ρ ∈ RvM.zerosIn (transformHeight X ν) B := by
        simpa only [H, Set.Finite.mem_toFinset] using hρ
      have hh := hz.2.1
      rw [resamplingZeroWeight, if_neg (not_le.mpr hh), gaussianTailZeroWeight]
      ring
  change (∑ ρ ∈ Z, _) < _
  rw [he]
  have hl := actual_low_gaussian_zero_bound X ν hX hν hν1
  have ht := actual_tail_gaussian_zero_bound X ν B hX hν hB
  have hm := add_le_add hl (mul_le_mul_of_nonneg_left ht
    (by positivity : 0 ≤ 4 / optimalWidth X ν^2))
  have hc := counting_loss_absorbed X ν hX hν hν1 hseed hk
  have hb := improved_balanced_envelope X ν hX hν hν1 hk
  change (∑ ρ ∈ L, _) + 4 / optimalWidth X ν^2 * (∑ ρ ∈ H, _) ≤ _ at hm
  have heR : improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) +
      2 * (9 * Real.log (transformHeight X ν + 5) + 79) * gaussianZeroWeight X (transformHeight X ν) +
      4 / optimalWidth X ν^2 * (upperEnvelope X (Real.log (2 * Real.pi)) (X * ν) / (2 * Real.pi) +
        2 * zeroCountErrorBound (transformHeight X ν) * gaussianTailZeroWeight X (transformHeight X ν) +
        9 * gaussianCountTailEnvelope X (X * ν)) =
      (improvedLowerEnvelope X (Real.log (2 * Real.pi)) (X * ν) +
        4 / optimalWidth X ν^2 * upperEnvelope X (Real.log (2 * Real.pi)) (X * ν)) / (2 * Real.pi) +
      (2 * zeroCountErrorBound (transformHeight X ν) * gaussianZeroWeight X (transformHeight X ν) +
        8 / optimalWidth X ν^2 * zeroCountErrorBound (transformHeight X ν) * gaussianTailZeroWeight X (transformHeight X ν) +
        36 / optimalWidth X ν^2 * gaussianCountTailEnvelope X (X * ν)) := by
    unfold zeroCountErrorBound
    ring
  rw [heR, hb] at hm
  linarith only [hm, hc]

lemma reflected_gaussian_window_bound (X ν B q : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (hν1 : ν ≤ 1) (hseed : seed X ≤ ν)
    (hk : k X ν = 1) (hB : transformHeight X ν ≤ B)
    (hq : 0 ≤ q) (hqb : q ≤ Real.exp (-4 * X)) :
    (∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im *
        Real.exp (-X^2 / Real.log ρ.im)) +
    q * (∑ ρ ∈ (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im) <
        optimalWidth X ν := by
  have hg := gaussian_window_weight_bound X ν B hX hν hν1 hseed hk hB
  have hw := finite_resampling_weight_bound X ν hX hν
    (RvM.finite_zero_window (b := B) (by norm_num : (0 : ℝ) < 4)).toFinset
    (fun ρ hρ => by
      have hh := hρ
      rw [Set.Finite.mem_toFinset] at hh
      exact ⟨hh.1, by linarith [hh.2.1]⟩)
  have hr := reflection_loss_absorbed X ν q hX hν hν1 hk hq hqb
  have hm := mul_le_mul_of_nonneg_left hw hq
  linarith

end DusartSmoothing


