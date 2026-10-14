-- Prove2me | Definitions.Def_dusart_psi_433_20261014_SymmetricWindows
-- name    : dusart_psi_433_20261014_SymmetricWindows
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:30:39.074217+00:00
-- url     : https://prove2.me/theorems/9c6d8fe6-4f4a-4068-a302-fef986ba055d
-- title:
--   Dusart smoothing: Symmetric Windows
-- statement:
--   This module gives the complete symmetric windows component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_LowCutoff
import Definitions.Def_dusart_psi_433_20261014_AllHeights
noncomputable section
namespace DusartSmoothing.RvM
open Complex Set Topology Filter Real

lemma nontrivial_zero_abs_height (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    2 * Real.pi < |ρ.im| :=
  DusartSmoothing.LowHeight.nontrivial_zero_height_gt_two_pi ρ hρ.1 hρ.2.1 hρ.2.2

lemma zerosIn_zero_eq_four (T : ℝ) : zerosIn 0 T = zerosIn 4 T := by
  ext ρ
  constructor
  · rintro ⟨hρ, ht0, htT⟩
    have hheight := nontrivial_zero_abs_height ρ hρ
    rw [abs_of_pos ht0] at hheight
    exact ⟨hρ, by linarith [Real.pi_gt_three], htT⟩
  · rintro ⟨hρ, ht4, htT⟩
    exact ⟨hρ, by linarith, htT⟩

lemma Ncount_zero_eq_four (T : ℝ) : Ncount 0 T = Ncount 4 T := by
  simp only [Ncount, zerosIn_zero_eq_four]

lemma positive_zero_count_error (T : ℝ) (hT : 4 ≤ T) :
    |(Ncount 0 T : ℝ) - countingMain T| ≤ 9 * Real.log (T + 5) + 79 := by
  rw [Ncount_zero_eq_four]
  exact Ncount_four_error T hT

lemma goodHeight_neg {T : ℝ} (hg : GoodHeight T) : GoodHeight (-T) := by
  intro ρ hρ he
  have hc : IsNontrivialZero (starRingEnd ℂ ρ) := by
    refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩
    rw [riemannZeta_conj, hρ.1, map_zero]
  apply hg (starRingEnd ℂ ρ) hc
  simp [he]

lemma finite_symmetric_zero_window (T : ℝ) :
    {ρ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.Finite := by
  have hp : (zerosIn 4 T).Finite := finite_zero_window (by norm_num : (0 : ℝ) < 4)
  refine (hp.union (hp.image (starRingEnd ℂ))).subset ?_
  rintro ρ ⟨hρ, him⟩
  have hγ := nontrivial_zero_abs_height ρ hρ
  rcases le_total 0 ρ.im with hpos | hneg
  · left
    rw [abs_of_nonneg hpos] at hγ him
    exact ⟨hρ, by linarith [Real.pi_gt_three], him⟩
  · right
    refine ⟨starRingEnd ℂ ρ, ?_, by simp⟩
    refine ⟨⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩, ?_, ?_⟩
    · rw [riemannZeta_conj, hρ.1, map_zero]
    · rw [Complex.conj_im]
      rw [abs_of_nonpos hneg] at hγ
      linarith [Real.pi_gt_three]
    · rw [Complex.conj_im]
      rwa [abs_of_nonpos hneg] at him

end DusartSmoothing.RvM


