-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ActualAbel
-- name    : dusart_psi_433_20261014_ActualAbel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:35:23.51404+00:00
-- url     : https://prove2.me/theorems/7d32c1da-bc70-4f0e-b2d8-1a18f5a3d3d7
-- title:
--   Dusart smoothing: Actual Abel
-- statement:
--   This module gives the complete actual abel component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WeightedCount
noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

lemma actual_window_count_eq (T t : ℝ) (ht : 4 ≤ t) (htT : t ≤ T) :
    finiteZeroCount (RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)).toFinset
      RvM.zeroMult Complex.im t = (RvM.Ncount 0 t : ℝ) := by
  classical
  let hT := RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)
  let ht' := RvM.finite_zero_window (b := t) (by norm_num : (0 : ℝ) < 4)
  have he : hT.toFinset.filter (fun ρ => ρ.im ≤ t) = ht'.toFinset := by
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hρ, hl, _⟩, hu⟩
      exact ⟨hρ, hl, hu⟩
    · rintro ⟨hρ, hl, hu⟩
      exact ⟨⟨hρ, hl, hu.trans htT⟩, hu⟩
  rw [RvM.Ncount_zero_eq_four, RvM.Ncount,
    finsum_mem_eq_finite_toFinset_sum _ ht', Nat.cast_sum, ← he]
  simp [finiteZeroCount, primeStep, Finset.sum_filter, mul_ite]

lemma actual_zero_summation_by_parts (T : ℝ) (hT : 2 * Real.pi ≤ T)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Set.Icc (2 * Real.pi) T))
    (hderiv : ∀ t ∈ Set.Icc (2 * Real.pi) T, HasDerivAt g (g' t) t) :
    (∑ ρ ∈ (RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * g ρ.im) =
      g T * (RvM.Ncount 0 T : ℝ) -
        ∫ t in (2 * Real.pi)..T, (RvM.Ncount 0 t : ℝ) * g' t := by
  classical
  let hf := RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)
  have hZ : ∀ ρ ∈ hf.toFinset, 2 * Real.pi ≤ ρ.im ∧ ρ.im ≤ T := by
    intro ρ hρ
    obtain ⟨hnt, hl, hu⟩ := hf.mem_toFinset.mp hρ
    have hg := RvM.nontrivial_zero_abs_height ρ hnt
    rw [abs_of_pos (by linarith : 0 < ρ.im)] at hg
    exact ⟨hg.le, hu⟩
  have h := finite_zero_summation_by_parts hf.toFinset RvM.zeroMult Complex.im
    (2 * Real.pi) T hT hZ g g' hcont hderiv
  have he : (∑ ρ ∈ hf.toFinset, (RvM.zeroMult ρ : ℝ)) = (RvM.Ncount 0 T : ℝ) := by
    rw [RvM.Ncount_zero_eq_four, RvM.Ncount, finsum_mem_eq_finite_toFinset_sum _ hf, Nat.cast_sum]
  have hi : (∫ t in (2 * Real.pi)..T, finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t * g' t) =
      ∫ t in (2 * Real.pi)..T, (RvM.Ncount 0 t : ℝ) * g' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    change finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t * g' t = _
    dsimp only [hf]
    rw [actual_window_count_eq T t (by linarith [ht.1, Real.pi_gt_three]) ht.2]
  rw [he, hi] at h
  exact h

end DusartSmoothing


