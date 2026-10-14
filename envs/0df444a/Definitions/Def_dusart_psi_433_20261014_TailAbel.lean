-- Prove2me | Definitions.Def_dusart_psi_433_20261014_TailAbel
-- name    : dusart_psi_433_20261014_TailAbel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:40:14.884086+00:00
-- url     : https://prove2.me/theorems/667c916a-4baf-4b37-be3b-beceb1776577
-- title:
--   Dusart smoothing: Tail Abel
-- statement:
--   This module gives the complete tail abel component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ZeroCountIntervals
noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

lemma actual_zero_interval_summation_by_parts (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b)
    (g g' : ℝ → ℝ) (hcont : ContinuousOn g' (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) :
    (∑ ρ ∈ (RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)).toFinset,
      (RvM.zeroMult ρ : ℝ) * g ρ.im) =
      g b * (RvM.Ncount 0 b : ℝ) - g a * (RvM.Ncount 0 a : ℝ) -
        ∫ t in a..b, (RvM.Ncount 0 t : ℝ) * g' t := by
  classical
  let hf := RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)
  have hγ : ∀ ρ ∈ hf.toFinset, a ≤ ρ.im ∧ ρ.im ≤ b := by
    intro ρ hρ
    obtain ⟨_, hl, hu⟩ := hf.mem_toFinset.mp hρ
    exact ⟨hl.le, hu⟩
  have hs := finite_zero_summation_by_parts hf.toFinset RvM.zeroMult Complex.im a b hab hγ
    g g' hcont hderiv
  have hc : (∑ ρ ∈ hf.toFinset, (RvM.zeroMult ρ : ℝ)) =
      (RvM.Ncount 0 b : ℝ) - (RvM.Ncount 0 a : ℝ) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (actual_count_add a b ha hab)
    push_cast at hh
    have he : (RvM.Ncount a b : ℝ) = ∑ ρ ∈ hf.toFinset, (RvM.zeroMult ρ : ℝ) := by
      rw [RvM.Ncount, finsum_mem_eq_finite_toFinset_sum _ hf, Nat.cast_sum]
    rw [he] at hh
    linarith
  have hig : IntervalIntegrable g' volume a b := hcont.intervalIntegrable_of_Icc hab
  have hNg := intervalIntegrable_actual_count_mul_from a b ha hab g' hcont
  have hgFTC : (∫ t in a..b, g' t) = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by simpa only [uIcc_of_le hab] using ht)) hig
  have hInt : (∫ t in a..b, finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t * g' t) =
      (∫ t in a..b, (RvM.Ncount 0 t : ℝ) * g' t) -
        (RvM.Ncount 0 a : ℝ) * (g b - g a) := by
    have he : (∫ t in a..b, finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t * g' t) =
        ∫ t in a..b, ((RvM.Ncount 0 t : ℝ) * g' t - (RvM.Ncount 0 a : ℝ) * g' t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      change finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t * g' t = _
      rw [actual_interval_window_count_eq a b t ha ht.1 ht.2]
      ring
    rw [he, intervalIntegral.integral_sub hNg (hig.const_mul _),
      intervalIntegral.integral_const_mul, hgFTC]
  rw [hs, hc, hInt]
  ring

end DusartSmoothing


