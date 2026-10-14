-- Prove2me | Definitions.Def_dusart_psi_433_20261014_IncreasingWeight
-- name    : dusart_psi_433_20261014_IncreasingWeight
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:38:29.533247+00:00
-- url     : https://prove2.me/theorems/90696504-a9a5-49e8-b37e-61a868a0b1fc
-- title:
--   Dusart smoothing: Increasing Weight
-- statement:
--   This module gives the complete increasing weight component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ActualAbel
noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

lemma intervalIntegrable_actual_count_mul (T : ℝ) (hT : 2 * Real.pi ≤ T)
    (g' : ℝ → ℝ) (hc : ContinuousOn g' (Icc (2 * Real.pi) T)) :
    IntervalIntegrable (fun t => (RvM.Ncount 0 t : ℝ) * g' t) volume (2 * Real.pi) T := by
  classical
  let Z := (RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)).toFinset
  have hi : IntervalIntegrable (fun t => finiteZeroCount Z RvM.zeroMult Complex.im t * g' t)
      volume (2 * Real.pi) T := by
    have he : (fun t => finiteZeroCount Z RvM.zeroMult Complex.im t * g' t) =
        fun t => ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * primeStep ρ.im t * g' t := by
      funext t; rw [finiteZeroCount, Finset.sum_mul]
    rw [he]
    have hρ : ∀ ρ ∈ Z, IntervalIntegrable
        (fun t => (RvM.zeroMult ρ : ℝ) * primeStep ρ.im t * g' t) volume (2 * Real.pi) T := by
      intro ρ _
      exact (((primeStep_mono ρ.im).intervalIntegrable (μ := volume)).const_mul
        (RvM.zeroMult ρ : ℝ)).mul_continuousOn
          (by simpa only [uIcc_of_le hT] using hc)
    have hs := IntervalIntegrable.sum Z hρ
    convert hs using 1 <;> try rfl
    funext t
    simp only [Finset.sum_apply]

  apply hi.congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  change finiteZeroCount Z RvM.zeroMult Complex.im t * g' t = _
  rw [actual_window_count_eq T t (by linarith [ht.1, Real.pi_gt_three]) ht.2]

lemma actual_increasing_zero_weight_bound (T : ℝ) (hT : 2 * Real.pi ≤ T)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc (2 * Real.pi) T))
    (hderiv : ∀ t ∈ Icc (2 * Real.pi) T, HasDerivAt g (g' t) t)
    (hg : ∀ t ∈ Icc (2 * Real.pi) T, 0 ≤ g t)
    (hg' : ∀ t ∈ Icc (2 * Real.pi) T, 0 ≤ g' t) :
    (∑ ρ ∈ (RvM.finite_zero_window (b := T) (by norm_num : (0 : ℝ) < 4)).toFinset,
      (RvM.zeroMult ρ : ℝ) * g ρ.im) ≤
      (∫ t in (2 * Real.pi)..T, (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi)) * g t) +
        2 * (9 * Real.log (T + 5) + 79) * g T := by
  let a : ℝ := 2 * Real.pi
  let E : ℝ := 9 * Real.log (T + 5) + 79
  let F : ℝ → ℝ := RvM.countingMain
  let D : ℝ → ℝ := fun t => 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi))
  have ha : 0 < a := by dsimp [a]; positivity
  have hTa : a ≤ T := hT
  have hT4 : 4 ≤ T := by linarith [Real.pi_gt_three]
  have hE : 0 ≤ E := by
    have hl : 0 ≤ Real.log (T + 5) := Real.log_nonneg (by linarith)
    dsimp [E]
    linarith
  have hgc : ContinuousOn g (Icc a T) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (Icc a T) := fun t ht =>
    (RvM.hasDerivAt_countingMain t (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc a T) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.log
    · fun_prop
    · intro t ht
      exact (div_pos (ha.trans_le ht.1) (by positivity)).ne'
  have hiFG : IntervalIntegrable (fun t => F t * g' t) volume a T :=
    (hFc.mul hcont).intervalIntegrable_of_Icc hTa
  have hiDg : IntervalIntegrable (fun t => D t * g t) volume a T :=
    (hDc.mul hgc).intervalIntegrable_of_Icc hTa
  have hig : IntervalIntegrable g' volume a T := hcont.intervalIntegrable_of_Icc hTa
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (RvM.hasDerivAt_countingMain t (by rw [uIcc_of_le hTa] at ht; exact ha.trans_le ht.1)).mul
      (hderiv t (by simpa only [uIcc_of_le hTa] using ht))) (hiDg.add hiFG)
  change (∫ t in a..T, D t * g t + F t * g' t) = F T * g T - F a * g a at hFTC
  rw [intervalIntegral.integral_add hiDg hiFG] at hFTC
  have hgFTC : (∫ t in a..T, g' t) = g T - g a := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa only [uIcc_of_le hTa] using ht)) hig
  have hFa : F a = -1 := by norm_num [F, a, RvM.countingMain, Real.pi_ne_zero]
  have hupper : (RvM.Ncount 0 T : ℝ) ≤ F T + E := by
    have h := (abs_le.mp (RvM.positive_zero_count_error T hT4)).2
    dsimp [F, E]
    linarith
  have hlower : ∀ t ∈ Icc a T, F t - E ≤ (RvM.Ncount 0 t : ℝ) := by
    intro t ht
    have ht4 : 4 ≤ t := by dsimp [a] at ht; linarith [ht.1, Real.pi_gt_three]
    have h := (abs_le.mp (RvM.positive_zero_count_error t ht4)).1
    have he : Real.log (t + 5) ≤ Real.log (T + 5) :=
      Real.log_le_log (by linarith) (by linarith [ht.2])
    dsimp [F, E]
    linarith
  have hiLower : IntervalIntegrable (fun t => (F t - E) * g' t) volume a T :=
    ((hFc.sub continuousOn_const).mul hcont).intervalIntegrable_of_Icc hTa
  have hInt : (∫ t in a..T, (F t - E) * g' t) ≤
      ∫ t in a..T, (RvM.Ncount 0 t : ℝ) * g' t := by
    apply intervalIntegral.integral_mono_on hTa hiLower (intervalIntegrable_actual_count_mul T hT g' hcont)
    intro t ht
    exact mul_le_mul_of_nonneg_right (hlower t ht) (hg' t ht)
  have heLower : (∫ t in a..T, (F t - E) * g' t) =
      (∫ t in a..T, F t * g' t) - E * (g T - g a) := by
    have he : (fun t => (F t - E) * g' t) = fun t => F t * g' t - E * g' t := by funext t; ring
    rw [he, intervalIntegral.integral_sub hiFG (hig.const_mul E), intervalIntegral.integral_const_mul, hgFTC]
  rw [heLower] at hInt
  have hboundary := mul_le_mul_of_nonneg_right hupper (hg T ⟨hTa, le_rfl⟩)
  have hga := hg a ⟨le_rfl, hTa⟩
  have hEa := mul_nonneg hE hga
  rw [hFa] at hFTC
  rw [actual_zero_summation_by_parts T hT g g' hcont hderiv]
  change g T * (RvM.Ncount 0 T : ℝ) - _ ≤ (∫ t in a..T, D t * g t) + 2 * E * g T
  nlinarith

end DusartSmoothing


