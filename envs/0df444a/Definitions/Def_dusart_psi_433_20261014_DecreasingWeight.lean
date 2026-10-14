-- Prove2me | Definitions.Def_dusart_psi_433_20261014_DecreasingWeight
-- name    : dusart_psi_433_20261014_DecreasingWeight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:41:15.828803+00:00
-- url     : https://prove2.me/theorems/688b9b51-f50b-45b3-a2d7-f0f238c984fc
-- title:
--   Dusart smoothing: Decreasing Weight
-- statement:
--   This module gives the complete decreasing weight component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_TailAbel
noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

noncomputable def zeroCountErrorBound (t : ℝ) : ℝ := 9 * Real.log (t + 5) + 79

lemma hasDerivAt_zeroCountErrorBound (t : ℝ) (ht : 4 ≤ t) :
    HasDerivAt zeroCountErrorBound (9 / (t + 5)) t := by
  convert ((((hasDerivAt_id t).add_const 5).log (by linarith : t + 5 ≠ 0)).const_mul 9).add_const 79 using 1 <;> try rfl
  dsimp
  ring

lemma actual_decreasing_zero_weight_bound (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hg : ∀ t ∈ Icc a b, 0 ≤ g t) (hg' : ∀ t ∈ Icc a b, g' t ≤ 0) :
    (∑ ρ ∈ (RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)).toFinset,
      (RvM.zeroMult ρ : ℝ) * g ρ.im) ≤
      (∫ t in a..b, ((1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) + 9 / (t + 5)) * g t) +
        2 * zeroCountErrorBound a * g a := by
  let Φ : ℝ → ℝ := fun t => RvM.countingMain t + zeroCountErrorBound t
  let D : ℝ → ℝ := fun t => (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) + 9 / (t + 5)
  have hp : ∀ t ∈ Icc a b, 0 < t := fun t ht => by linarith [ht.1]
  have hΦd : ∀ t ∈ Icc a b, HasDerivAt Φ (D t) t := fun t ht =>
    (RvM.hasDerivAt_countingMain t (hp t ht)).add
      (hasDerivAt_zeroCountErrorBound t (ha.trans ht.1))
  have hΦc : ContinuousOn Φ (Icc a b) := fun t ht => (hΦd t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc a b) := by
    intro t ht
    have htn : t ≠ 0 := (hp t ht).ne'
    have hden : t / (2 * Real.pi) ≠ 0 := div_ne_zero htn (by positivity)
    have ht5 : t + 5 ≠ 0 := by linarith [hp t ht]
    dsimp [D]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  have hiDg : IntervalIntegrable (fun t => D t * g t) volume a b :=
    (hDc.mul hgc).intervalIntegrable_of_Icc hab
  have hiΦg : IntervalIntegrable (fun t => Φ t * g' t) volume a b :=
    (hΦc.mul hcont).intervalIntegrable_of_Icc hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hΦd t (by simpa only [uIcc_of_le hab] using ht)).mul
      (hderiv t (by simpa only [uIcc_of_le hab] using ht))) (hiDg.add hiΦg)
  change (∫ t in a..b, D t * g t + Φ t * g' t) = Φ b * g b - Φ a * g a at hFTC
  rw [intervalIntegral.integral_add hiDg hiΦg] at hFTC
  have hupper : ∀ t ∈ Icc a b, (RvM.Ncount 0 t : ℝ) ≤ Φ t := by
    intro t ht
    have h := (abs_le.mp (RvM.positive_zero_count_error t (ha.trans ht.1))).2
    dsimp [Φ, zeroCountErrorBound]
    linarith
  have hlower : Φ a - 2 * zeroCountErrorBound a ≤ (RvM.Ncount 0 a : ℝ) := by
    have h := (abs_le.mp (RvM.positive_zero_count_error a ha)).1
    dsimp [Φ, zeroCountErrorBound]
    linarith
  have hInt : (∫ t in a..b, Φ t * g' t) ≤ ∫ t in a..b, (RvM.Ncount 0 t : ℝ) * g' t := by
    apply intervalIntegral.integral_mono_on hab hiΦg (intervalIntegrable_actual_count_mul_from a b ha hab g' hcont)
    intro t ht
    exact mul_le_mul_of_nonpos_right (hupper t ht) (hg' t ht)
  have hb := mul_le_mul_of_nonneg_right (hupper b ⟨hab, le_rfl⟩) (hg b ⟨hab, le_rfl⟩)
  have ha' := mul_le_mul_of_nonneg_right hlower (hg a ⟨le_rfl, hab⟩)
  rw [actual_zero_interval_summation_by_parts a b ha hab g g' hcont hderiv]
  change g b * (RvM.Ncount 0 b : ℝ) - g a * (RvM.Ncount 0 a : ℝ) - _ ≤
    (∫ t in a..b, D t * g t) + 2 * zeroCountErrorBound a * g a
  nlinarith

end DusartSmoothing


