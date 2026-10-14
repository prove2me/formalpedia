-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PsiComparison
-- name    : dusart_psi_433_20261014_PsiComparison
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:17:23.859108+00:00
-- url     : https://prove2.me/theorems/b9573fee-74b6-4259-89fa-678109f1b2be
-- title:
--   Dusart smoothing: Psi Comparison
-- statement:
--   This module gives the complete psi comparison component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_Parameters
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace DusartSmoothing

noncomputable def boxAverage (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..h, f (x + t)) / h

noncomputable def doubleBoxAverage (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  boxAverage (fun y => boxAverage f y h) x h

lemma boxAverage_mono (f : ℝ → ℝ) (hf : Monotone f) (h : ℝ) (hh : 0 < h) :
    Monotone (fun x => boxAverage f x h) := by
  intro x y hxy
  apply (div_le_div_iff_of_pos_right hh).2
  apply intervalIntegral.integral_mono_on hh.le
    ((hf.comp (monotone_const.add monotone_id)).intervalIntegrable)
    ((hf.comp (monotone_const.add monotone_id)).intervalIntegrable)
  intro t ht
  exact hf (by linarith)

lemma boxAverage_bounds (f : ℝ → ℝ) (hf : Monotone f) (x h : ℝ) (hh : 0 < h) :
    f x ≤ boxAverage f x h ∧ boxAverage f x h ≤ f (x + h) := by
  have hi : IntervalIntegrable (fun t : ℝ => f (x + t)) volume 0 h :=
    (hf.comp (monotone_const.add monotone_id)).intervalIntegrable
  have hl := intervalIntegral.integral_mono_on hh.le intervalIntegrable_const hi
    (fun t ht => hf (show x ≤ x + t by linarith [ht.1]))
  have hu := intervalIntegral.integral_mono_on hh.le hi intervalIntegrable_const
    (fun t ht => hf (show x + t ≤ x + h by linarith [ht.2]))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl hu
  constructor
  · exact (le_div_iff₀ hh).2 (by simpa only [mul_comm] using hl)
  · exact (div_le_iff₀ hh).2 (by simpa only [mul_comm] using hu)

theorem doubleBoxAverage_bounds (f : ℝ → ℝ) (hf : Monotone f)
    (x h : ℝ) (hh : 0 < h) :
    f x ≤ doubleBoxAverage f x h ∧ doubleBoxAverage f x h ≤ f (x + 2 * h) := by
  have h₁ := boxAverage_bounds f hf x h hh
  have h₂ := boxAverage_bounds (fun y => boxAverage f y h)
    (boxAverage_mono f hf h hh) x h hh
  have h₃ := boxAverage_bounds f hf (x + h) h hh
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  simpa only [doubleBoxAverage, show x + h + h = x + 2 * h by ring] using
    h₂.2.trans h₃.2

lemma boxAverage_affine (x h c : ℝ) (hh : h ≠ 0) :
    boxAverage (fun y => y + c) x h = x + c + h / 2 := by
  have heq : (fun t : ℝ => x + t + c) = (fun t => (x + c) + t) := by
    funext t
    ring
  dsimp [boxAverage]
  rw [heq]
  have hi : (∫ t in (0 : ℝ)..h, x + c + t) =
      (∫ _ in (0 : ℝ)..h, x + c) + (∫ t in (0 : ℝ)..h, t) := by
    exact intervalIntegral.integral_add intervalIntegrable_const
      (continuous_id.intervalIntegrable 0 h)
  rw [hi]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_id,
    sub_zero]
  field_simp
  ring

lemma doubleBoxAverage_identity (x h : ℝ) (hh : h ≠ 0) :
    doubleBoxAverage (fun y => y) x h = x + h := by
  have hid : (fun y => boxAverage (fun z : ℝ => z) y h) = (fun y => y + h / 2) := by
    funext y
    simpa using boxAverage_affine y h 0 hh
  dsimp [doubleBoxAverage]
  rw [hid, boxAverage_affine x h (h / 2) hh]
  ring

theorem psi_between_double_averages (x h : ℝ) (hh : 0 < h) :
    doubleBoxAverage Chebyshev.psi (x - 2 * h) h ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤ doubleBoxAverage Chebyshev.psi x h := by
  have hl := (doubleBoxAverage_bounds Chebyshev.psi Chebyshev.psi_mono
    (x - 2 * h) h hh).2
  have hu := (doubleBoxAverage_bounds Chebyshev.psi Chebyshev.psi_mono x h hh).1
  exact ⟨by simpa using hl, hu⟩

theorem psi_error_of_double_average_errors (x h E : ℝ) (hh : 0 < h)
    (hl : |doubleBoxAverage Chebyshev.psi (x - 2 * h) h - (x - h)| ≤ E)
    (hu : |doubleBoxAverage Chebyshev.psi x h - (x + h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + h := by
  have hb := psi_between_double_averages x h hh
  have hll := (abs_le.mp hl).1
  have huu := (abs_le.mp hu).2
  apply abs_le.mpr
  constructor <;> linarith

theorem psi_error_of_double_average_errors_strict (x h E : ℝ) (hh : 0 < h)
    (hl : |doubleBoxAverage Chebyshev.psi (x - 2 * h) h - (x - h)| < E)
    (hu : |doubleBoxAverage Chebyshev.psi x h - (x + h)| < E) :
    |Chebyshev.psi x - x| < E + h := by
  have hb := psi_between_double_averages x h hh
  have hll := (abs_lt.mp hl).1
  have huu := (abs_lt.mp hu).2
  apply abs_lt.mpr
  constructor <;> linarith

end DusartSmoothing


