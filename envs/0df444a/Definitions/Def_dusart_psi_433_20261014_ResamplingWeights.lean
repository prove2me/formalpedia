-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ResamplingWeights
-- name    : dusart_psi_433_20261014_ResamplingWeights
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:45:50.649548+00:00
-- url     : https://prove2.me/theorems/fd5002a4-05df-4d46-b76a-901847374dfd
-- title:
--   Dusart smoothing: Resampling Weights
-- statement:
--   This module gives the complete resampling weights component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_HeightBounds
import Definitions.Def_dusart_psi_433_20261014_LowGaussian
import Definitions.Def_dusart_psi_433_20261014_TailGaussian
import Definitions.Def_dusart_psi_433_20261014_InverseHeight
import Definitions.Def_dusart_psi_433_20261014_PositiveZeroSeries
noncomputable section
namespace DusartSmoothing
open Real Complex

noncomputable def resamplingZeroWeight (δ T t : ℝ) : ℝ :=
  if t ≤ T then 1 / t else 4 / (δ^2 * t^3)

lemma resamplingZeroWeight_nonneg (δ T t : ℝ) (ht : 0 < t) :
    0 ≤ resamplingZeroWeight δ T t := by
  unfold resamplingZeroWeight
  split_ifs <;> positivity

lemma finite_resampling_weight_bound (X ν : ℝ) (hX : (836 / 100 : ℝ) < X)
    (hν : (97 / 100 : ℝ) < ν) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im) ≤
        32 * transformHeight X ν + 48 / optimalWidth X ν^2 := by
  classical
  let L := Z.filter (fun ρ => ρ.im ≤ transformHeight X ν)
  let H := Z.filter (fun ρ => ¬ρ.im ≤ transformHeight X ν)
  have hL : ∀ ρ ∈ L, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im :=
    fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1
  have hH : ∀ ρ ∈ H, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im :=
    fun ρ hρ => hZ ρ (Finset.mem_filter.mp hρ).1
  have hT4 : 4 ≤ transformHeight X ν := by
    linarith [transformHeight_gt_five_hundred X ν hX hν]
  have hl := finite_positive_inverse_height_le L hL (transformHeight X ν) hT4
    (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hh := finite_positive_inverse_cube_bound H hH
  have hδ := optimalWidth_pos X ν hX hν
  have he : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      resamplingZeroWeight (optimalWidth X ν) (transformHeight X ν) ρ.im) =
      (∑ ρ ∈ L, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) +
        4 / optimalWidth X ν^2 * ∑ ρ ∈ H, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3) := by
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.im ≤ transformHeight X ν)]
    congr 1
    · apply Finset.sum_congr rfl
      intro ρ hρ
      simp only [resamplingZeroWeight, if_pos (Finset.mem_filter.mp hρ).2]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [resamplingZeroWeight, if_neg (Finset.mem_filter.mp hρ).2]
      ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4 / optimalWidth X ν^2)
  rw [show 4 / optimalWidth X ν^2 * 12 = 48 / optimalWidth X ν^2 by ring] at hm
  exact add_le_add hl hm

end DusartSmoothing


