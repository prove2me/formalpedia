-- Prove2me | Definitions.Def_dusart_psi_433_20261014_InverseCube
-- name    : dusart_psi_433_20261014_InverseCube
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:36:44.871377+00:00
-- url     : https://prove2.me/theorems/6af9b2ed-a023-42bb-a2d7-58944ad86d88
-- title:
--   Dusart smoothing: Inverse Cube
-- statement:
--   This module gives the complete inverse cube component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_WeightedCount
noncomputable section
namespace DusartSmoothing
open Complex Set MeasureTheory

lemma finite_positive_inverse_cube_le (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (b : ℝ) (hb : 4 ≤ b) (hγ : ∀ ρ ∈ Z, ρ.im ≤ b) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤ 12 := by
  let g : ℝ → ℝ := fun t => 1 / t^3
  let d : ℝ → ℝ := fun t => -3 / t^4
  have hcont : ContinuousOn d (Icc 4 b) := by
    intro t ht
    have hn : t ≠ 0 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    dsimp [d]
    fun_prop (disch := positivity)
  have hd : ∀ t ∈ Icc 4 b, HasDerivAt g (d t) t := by
    intro t ht
    have hn : t ≠ 0 := by linarith [ht.1]
    have h := ((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 hn)
    have he : (id ^ 3 : ℝ → ℝ)⁻¹ = g := by funext u; simp [g]
    rw [he] at h
    exact h.congr_deriv (by dsimp [d]; field_simp [hn] <;> ring)
  have hγ' : ∀ ρ ∈ Z, (4 : ℝ) ≤ ρ.im ∧ ρ.im ≤ b := by
    intro ρ hρ
    obtain ⟨hnt, hp⟩ := hZ ρ hρ
    have hh := RvM.nontrivial_zero_abs_height ρ hnt
    rw [abs_of_pos hp] at hh
    exact ⟨by linarith [Real.pi_gt_three], hγ ρ hρ⟩
  have ha := finite_zero_summation_by_parts Z RvM.zeroMult Complex.im 4 b hb hγ' g d hcont hd
  have hi : IntervalIntegrable (fun t => finiteZeroCount Z RvM.zeroMult Complex.im t * d t)
      volume 4 b := by
    have hQ : IntervalIntegrable (finiteZeroCount Z RvM.zeroMult Complex.im) volume 4 b := by
      change IntervalIntegrable (fun t => ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * primeStep ρ.im t) volume 4 b
      have hs := IntervalIntegrable.sum Z (fun ρ _ =>
        ((primeStep_mono ρ.im).intervalIntegrable (μ := volume) (a := 4) (b := b)).const_mul
          (RvM.zeroMult ρ : ℝ))
      convert hs using 1 <;> try rfl
      funext t
      simp only [Finset.sum_apply]
    exact hQ.mul_continuousOn (by simpa [uIcc_of_le hb] using hcont)
  have himaj : IntervalIntegrable (fun t => (16 * t^2) * d t) volume 4 b :=
    ((by fun_prop : Continuous (fun t : ℝ => 16 * t^2)).intervalIntegrable (μ := volume) 4 b).mul_continuousOn
      (by simpa [uIcc_of_le hb] using hcont)
  have hile : (∫ t in (4 : ℝ)..b, (16 * t^2) * d t) ≤
      ∫ t in (4 : ℝ)..b, finiteZeroCount Z RvM.zeroMult Complex.im t * d t := by
    apply intervalIntegral.integral_mono_on hb himaj hi
    intro t ht
    exact mul_le_mul_of_nonpos_right (finite_actual_zero_count_le_square Z hZ t ht.1)
      (by dsimp [d]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hival : (∫ t in (4 : ℝ)..b, (16 * t^2) * d t) = -48 * (1/4 - 1/b) := by
    have he : (∫ t in (4 : ℝ)..b, (16 * t^2) * d t) = ∫ t in (4 : ℝ)..b, -48 * (1/t^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hb] at ht
      have hn : t ≠ 0 := by linarith [ht.1]
      dsimp [d]
      field_simp [hn]
      ring
    rw [he, intervalIntegral.integral_const_mul,
      RvM.integral_reciprocal_square 4 b (by norm_num) hb]
  have hQb : finiteZeroCount Z RvM.zeroMult Complex.im b = ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [primeStep, hγ ρ hρ]
  have hc := finite_actual_zero_count_le_square Z hZ b hb
  rw [hQb] at hc
  have hbp : 0 < b := by linarith
  have hterm : g b * (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ 16 / b := by
    dsimp [g]
    have hh := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 1 / b^3)
    have he : (1 / b^3) * (16 * b^2) = 16 / b := by field_simp [hbp.ne'] <;> ring
    rwa [he] at hh
  rw [hival] at hile
  change (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ 12
  rw [ha]
  norm_num [div_eq_mul_inv] at hterm hile
  have hbinv : 0 ≤ b⁻¹ := inv_nonneg.mpr hbp.le
  linarith

end DusartSmoothing


