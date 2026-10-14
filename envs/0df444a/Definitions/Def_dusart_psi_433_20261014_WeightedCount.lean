-- Prove2me | Definitions.Def_dusart_psi_433_20261014_WeightedCount
-- name    : dusart_psi_433_20261014_WeightedCount
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:34:03.021686+00:00
-- url     : https://prove2.me/theorems/6d25df37-9070-409d-857f-5104eefa5612
-- title:
--   Dusart smoothing: Weighted Count
-- statement:
--   This module gives the complete weighted count component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroAbel
noncomputable section
namespace DusartSmoothing
open Complex Set

lemma finite_actual_zero_count_le (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) (t : ℝ) :
    finiteZeroCount Z RvM.zeroMult Complex.im t ≤ (RvM.Ncount 0 t : ℝ) := by
  classical
  let F := Z.filter (fun ρ => ρ.im ≤ t)
  have he : finiteZeroCount Z RvM.zeroMult Complex.im t =
      ∑ ρ ∈ F, (RvM.zeroMult ρ : ℝ) := by
    simp [finiteZeroCount, F, primeStep, Finset.sum_filter, mul_ite]
  rw [he, RvM.Ncount_zero_eq_four]
  let hf := RvM.finite_zero_window (b := t) (by norm_num : (0 : ℝ) < 4)
  have hsub : F ⊆ hf.toFinset := by
    intro ρ hρ
    obtain ⟨hρZ, hρt⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hnt, hpos⟩ := hZ ρ hρZ
    have hheight := RvM.nontrivial_zero_abs_height ρ hnt
    rw [abs_of_pos hpos] at hheight
    rw [Set.Finite.mem_toFinset]
    exact ⟨hnt, by linarith [Real.pi_gt_three], hρt⟩
  rw [RvM.Ncount, finsum_mem_eq_finite_toFinset_sum _ hf, Nat.cast_sum]
  exact_mod_cast (Finset.sum_le_sum_of_subset hsub :
    (∑ ρ ∈ F, RvM.zeroMult ρ) ≤ ∑ ρ ∈ hf.toFinset, RvM.zeroMult ρ)

lemma finite_actual_zero_count_bound (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t) :
    finiteZeroCount Z RvM.zeroMult Complex.im t ≤
      RvM.countingMain t + 9 * Real.log (t + 5) + 79 := by
  have hh := (abs_le.mp (RvM.positive_zero_count_error t ht)).2
  have hc := finite_actual_zero_count_le Z hZ t
  linarith


lemma counting_majorant_le_square (t : ℝ) (ht : 4 ≤ t) :
    RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤ 16 * t^2 := by
  have htp : 0 < t := by linarith
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hratio : t / (2 * Real.pi) ≤ t := div_le_self htp.le hπ
  have hlog : Real.log (t / (2 * Real.pi)) ≤ t - 1 :=
    (Real.log_le_log (by positivity) hratio).trans (Real.log_le_sub_one_of_pos htp)
  have hF : RvM.countingMain t ≤ t^2 := by
    unfold RvM.countingMain
    calc t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)
        ≤ t / (2 * Real.pi) * (t - 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ t * (t - 2) := mul_le_mul_of_nonneg_right hratio (by linarith)
      _ ≤ t^2 := by nlinarith
  have hE := Real.log_le_sub_one_of_pos (by linarith : 0 < t + 5)
  nlinarith [mul_nonneg htp.le (by linarith : 0 ≤ t - 4)]

lemma finite_actual_zero_count_le_square (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t) :
    finiteZeroCount Z RvM.zeroMult Complex.im t ≤ 16 * t^2 :=
  (finite_actual_zero_count_bound Z hZ t ht).trans (counting_majorant_le_square t ht)

end DusartSmoothing


