-- Prove2me | solution 1 for Arxiv1810_02867.slowness_domain_operator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:59:48.738036+00:00
-- url     : https://prove2.me/submissions/4381c596-1dbc-4321-bd7c-1aa94edd2ec9

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace S70SD
open Arxiv1810_02867

lemma hd (a : ℂ) (ω s1 : ℝ) (y : ℝ) :
    deriv (fun y : ℝ => a * Complex.exp (Complex.I * ω * s1 * y)) y =
      a * (Complex.I * ω * s1) * Complex.exp (Complex.I * ω * s1 * y) := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * ω * s1 * (y : ℂ)) (Complex.I * ω * s1) y := by
    simpa using ((hasDerivAt_id y).ofReal_comp).const_mul (Complex.I * ω * s1)
  rw [((h1.cexp).const_mul a).deriv]; ring

lemma D1 (ω s1 : ℝ) (gamma : Fin 2 → ℝ) (a : ℂ) (y : ℝ) :
    D1op ω (fun _ => gamma) (fun y => a * Complex.exp (Complex.I * ω * s1 * y)) y =
      (Complex.I * ω * ((s1 - gamma 0 : ℝ) : ℂ) * a) * Complex.exp (Complex.I * ω * s1 * y) := by
  unfold D1op; rw [hd]; push_cast; ring

end S70SD

open Arxiv1810_02867 S70SD in
theorem solution (ω : ℝ) (hω : ω ≠ 0) (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ)
    (gamma : Fin 2 → ℝ) (hsym : beta 0 1 = beta 1 0) (hb11 : beta 0 0 ≠ 0)
    (hdet : (Matrix.of beta).det ≠ 0) (s1 : ℝ) (c : Fin 2 → ℂ) (x1 : ℝ) :
    opA ω (fun _ => alpha) (fun _ => beta) (fun _ => gamma)
        (fun y => c 0 * Complex.exp (Complex.I * ω * s1 * y))
        (fun y => c 1 * Complex.exp (Complex.I * ω * s1 * y)) x1 =
      Complex.exp (Complex.I * ω * s1 * x1) • (Atilde ω alpha beta gamma s1).mulVec c := by
  have hθ : thetaOf beta 1 1 ≠ 0 := by
    unfold thetaOf
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [Ring.inverse_eq_inv', hdet, hb11]
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  set E := fun y : ℝ => Complex.exp (Complex.I * ω * s1 * y) with hE
  have hin : (fun y : ℝ => ((bCoef beta 0 : ℝ) : ℂ) *
      D1op ω (fun _ => gamma) (fun y => c 0 * Complex.exp (Complex.I * ω * s1 * y)) y) =
      fun y : ℝ => (((bCoef beta 0 : ℝ) : ℂ) * (Complex.I * ω * ((s1 - gamma 0 : ℝ) : ℂ) * c 0)) *
        Complex.exp (Complex.I * ω * s1 * y) := by
    funext y; rw [D1]; ring
  have hin2 : (fun y : ℝ => ((dCoef beta : ℝ) : ℂ) * (c 1 * Complex.exp (Complex.I * ω * s1 * y))) =
      fun y : ℝ => (((dCoef beta : ℝ) : ℂ) * c 1) * Complex.exp (Complex.I * ω * s1 * y) := by
    funext y; ring
  funext i
  fin_cases i
  · simp only [opA, Fin.zero_eta, Matrix.cons_val_zero]
    rw [D1]
    simp only [Atilde, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast; ring
  · simp only [opA, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
    rw [hin, hin2, D1, D1]
    simp only [Atilde, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, s3sq]
    have hθc : ((thetaOf beta 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hθ
    push_cast
    field_simp
    ring
