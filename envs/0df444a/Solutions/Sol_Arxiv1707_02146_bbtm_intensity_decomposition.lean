-- Prove2me | solution 1 for Arxiv1707_02146.bbtm_intensity_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:39:45.531595+00:00
-- url     : https://prove2.me/submissions/d0a44eb0-b2d6-4a6c-80be-c83a66a8768f

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate
open Arxiv1707_02146

lemma normSq_add_cross (a b : ℂ) :
    (Complex.normSq (a + b) : ℂ) = (Complex.normSq a : ℂ) + Complex.normSq b +
      (conj a * b + conj (conj a * b)) := by
  rw [Complex.normSq_add]
  have : conj a * b + conj (conj a * b) = ((2 * (a * conj b).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [this]; push_cast; ring

lemma bbtm_mulVec {N m n : ℕ} (ER : Fin N → Fin m → ℂ)
    (T : Fin N → Matrix (Fin m) (Fin n) ℂ) (E : Fin n → ℂ) (x : Fin m) :
    (bbtm ER T *ᵥ E) x = ∑ i, conj (ER i x) * (T i *ᵥ E) x := by
  simp only [bbtm, effectiveTM, Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

lemma modField_smul {N m n : ℕ} (T : Fin N → Matrix (Fin m) (Fin n) ℂ) (c : ℂ) (E : Fin n → ℂ)
    (i : Fin N) (x : Fin m) :
    modulatedField T (fun _ => c • E) i x = c * modulatedField T (fun _ => E) i x := by
  simp [modulatedField, Matrix.mulVec_smul]

theorem solution {N m n : ℕ} (ER : Fin N → Fin m → ℂ)
    (T : Fin N → Matrix (Fin m) (Fin n) ℂ) :
    (∀ (Ein : Fin N → Fin n → ℂ) (x : Fin m),
      (broadbandIntensity ER T Ein x : ℂ) = (staticTerm ER T Ein x : ℂ) +
        ∑ i, (conj (ER i x) * modulatedField T Ein i x +
          conj (conj (ER i x) * modulatedField T Ein i x))) ∧
    (∀ (E : Fin n → ℂ) (φ : ℝ) (x : Fin m),
      broadbandIntensity ER T (fun _ => Complex.exp (φ * Complex.I) • E) x =
          staticTerm ER T (fun _ => E) x +
            2 * (Complex.exp (φ * Complex.I) * (bbtm ER T *ᵥ E) x).re ∧
        staticTerm ER T (fun _ => Complex.exp (φ * Complex.I) • E) x =
          staticTerm ER T (fun _ => E) x) := by
  have hnorm : ∀ φ : ℝ, Complex.normSq (Complex.exp (φ * Complex.I)) = 1 := by
    intro φ; rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hstatic : ∀ (E : Fin n → ℂ) (φ : ℝ) (x : Fin m),
      staticTerm ER T (fun _ => Complex.exp (φ * Complex.I) • E) x =
        staticTerm ER T (fun _ => E) x := by
    intro E φ x
    simp only [staticTerm, modField_smul, Complex.normSq_mul, hnorm, one_mul]
  refine ⟨fun Ein x => ?_, fun E φ x => ⟨?_, hstatic E φ x⟩⟩
  · simp only [broadbandIntensity, staticTerm]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [normSq_add_cross]
  · -- real version of the expansion
    set c := Complex.exp (φ * Complex.I)
    have h1 : ∀ i, Complex.normSq (ER i x + modulatedField T (fun _ => c • E) i x) =
        Complex.normSq (ER i x) + Complex.normSq (modulatedField T (fun _ => E) i x) +
          2 * (c * (conj (ER i x) * (T i *ᵥ E) x)).re := by
      intro i
      rw [Complex.normSq_add, modField_smul, Complex.normSq_mul, hnorm, one_mul]
      simp only [modulatedField, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
      ring
    simp only [broadbandIntensity, staticTerm, h1, bbtm_mulVec, Finset.mul_sum,
      Complex.re_sum, Finset.sum_add_distrib]

