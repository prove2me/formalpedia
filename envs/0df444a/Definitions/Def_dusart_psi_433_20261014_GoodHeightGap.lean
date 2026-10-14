-- Prove2me | Definitions.Def_dusart_psi_433_20261014_GoodHeightGap
-- name    : dusart_psi_433_20261014_GoodHeightGap
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:39:37.648877+00:00
-- url     : https://prove2.me/theorems/ada0db61-d29a-4d87-a6a2-e0b69455d9d2
-- title:
--   Dusart smoothing: Good Height Gap
-- statement:
--   This module gives the complete good height gap component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_FarPoint
import Definitions.Def_dusart_psi_433_20261014_ZeroCard
noncomputable section
namespace DusartSmoothing
open Complex Real Set Metric Filter Topology

lemma good_height_with_global_gap (j : ℕ) (hj : 7 ≤ j) :
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧ RvM.GoodHeight R ∧
      ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → ρ.im ≤ (j : ℝ) + 3 →
        1 / (2 * (16 * ((j : ℝ) + 3)^2 + 1)) ≤ |R - ρ.im| := by
  classical
  have hjR : (7 : ℝ) ≤ j := by exact_mod_cast hj
  let hf := RvM.finite_zero_window (b := (j : ℝ) + 3) (by norm_num : (0 : ℝ) < 4)
  let Z := hf.toFinset
  let S : Finset ℝ := Z.image Complex.im
  have hcard : (S.card : ℝ) ≤ 16 * ((j : ℝ) + 3)^2 := by
    have h1 : (S.card : ℝ) ≤ Z.card := by exact_mod_cast Finset.card_image_le
    exact h1.trans (RvM.positive_zero_window_card_bound _ (by linarith))
  obtain ⟨R, hR1, hR2, hgap⟩ := Landau.exists_far_point S (j : ℝ)
  have hδ : 1 / (2 * (16 * ((j : ℝ) + 3)^2 + 1)) ≤ 1 / (2 * ((S.card : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have havoid : ∀ ρ : ℂ, RvM.IsNontrivialZero ρ → 0 < ρ.im → ρ.im ≤ (j : ℝ) + 3 →
      1 / (2 * (16 * ((j : ℝ) + 3)^2 + 1)) ≤ |R - ρ.im| := by
    intro ρ hz hpos hupper
    have hl := RvM.nontrivial_zero_abs_height ρ hz
    rw [abs_of_pos hpos] at hl
    have hρ : ρ ∈ Z := hf.mem_toFinset.mpr ⟨hz, by linarith [Real.pi_gt_three], hupper⟩
    exact hδ.trans (hgap ρ.im (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩))
  refine ⟨R, hR1, hR2, ?_, havoid⟩
  intro ρ hz he
  have h := havoid ρ hz (by rw [he]; linarith) (by rw [he]; linarith)
  rw [he, sub_self, abs_zero] at h
  have hp : 0 < 1 / (2 * (16 * ((j : ℝ) + 3)^2 + 1)) := by positivity
  linarith

end DusartSmoothing


