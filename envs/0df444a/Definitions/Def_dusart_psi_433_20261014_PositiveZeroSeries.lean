-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PositiveZeroSeries
-- name    : dusart_psi_433_20261014_PositiveZeroSeries
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:37:30.443926+00:00
-- url     : https://prove2.me/theorems/0ec37bed-4ec8-4ccb-a27d-9394cf91c67e
-- title:
--   Dusart smoothing: Positive Zero Series
-- statement:
--   This module gives the complete positive zero series component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_InverseCube
import Definitions.Def_dusart_psi_433_20261014_Mellin
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace DusartSmoothing
open Complex Set

lemma finite_positive_inverse_cube_bound (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤ 12 := by
  classical
  rcases Z.eq_empty_or_nonempty with h | hn
  · rw [h]; simp
  · let b : ℝ := max 4 (Z.sup' hn Complex.im)
    exact finite_positive_inverse_cube_le Z hZ b (le_max_left _ _)
      (fun ρ hρ => (Finset.le_sup' Complex.im hρ).trans (le_max_right _ _))

abbrev PositiveZetaZero := {ρ : ℂ // RvM.IsNontrivialZero ρ ∧ 0 < ρ.im}

lemma positive_zero_inverse_cube_summable :
    Summable (fun ρ : PositiveZetaZero => (RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) := by
  classical
  apply summable_of_sum_le (c := 12) (fun ρ => by
    have hρ := ρ.property.2
    positivity)
  intro S
  let Z : Finset ℂ := S.image (fun ρ : PositiveZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hρ
    exact he ▸ τ.property
  have h := finite_positive_inverse_cube_bound Z hZ
  dsimp [Z] at h
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at h
  exact h

lemma positive_quadratic_zero_sum_summable (x : ℝ) (hx : 1 ≤ x) :
    Summable (fun ρ : PositiveZetaZero => (RvM.zeroMult ρ.val : ℂ) *
      mellin (quadraticPrimeWeight x) ρ.val) := by
  have hxp : 0 < x := by linarith
  apply (positive_zero_inverse_cube_summable.mul_left (x^3)).of_norm_bounded
  intro ρ
  have hnt := ρ.property.1
  have him := ρ.property.2
  have hMF := norm_quadratic_mellin_le x hxp ρ.val hnt.2.1 him.ne'
  rw [abs_of_pos him] at hMF
  have hp : x ^ (ρ.val.re + 2) ≤ x^3 := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (show ρ.val.re + 2 ≤ (3 : ℝ) by linarith [hnt.2.2])
    simpa using h
  rw [norm_mul, Complex.norm_natCast]
  calc (RvM.zeroMult ρ.val : ℝ) * ‖mellin (quadraticPrimeWeight x) ρ.val‖
      ≤ (RvM.zeroMult ρ.val : ℝ) * (x^3 / ρ.val.im^3) := by
        exact mul_le_mul_of_nonneg_left (hMF.trans
          (div_le_div_of_nonneg_right hp (by positivity))) (Nat.cast_nonneg _)
    _ = _ := by ring

end DusartSmoothing


