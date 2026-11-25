-- Prove2me | solution 1 for Arxiv1504_01000.relative_hellinger_bounds
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:58:05.843041+00:00
-- url     : https://prove2.me/submissions/96cfdcfc-ffe8-450d-a55b-056b8e4bd31b

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open Matrix ComplexOrder

namespace S69E
open Arxiv1504_01000

lemma hU (θ : ℝ) : (U3 θ)ᴴ * U3 θ = 1 := by
  have h := Real.cos_sq_add_sin_sq (2 * θ)
  have hc : ((Real.cos (2 * θ) : ℂ)) ^ 2 + ((Real.sin (2 * θ) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal]
  all_goals (first | (linear_combination hc) | ring)

lemma bnn (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (l : Fin 3) (θ : ℝ) :
    0 ≤ sigmaSq T l θ := by
  unfold sigmaSq rotT
  rw [Matrix.inv_eq_left_inv (hU θ)]
  have hP := hT.posSemidef.mul_mul_conjTranspose_same (U3 θ)
  have := hP.diag_nonneg (i := l)
  exact (Complex.nonneg_iff.mp this).1

lemma hg (a b L : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hL : 0 < L) :
    0 ≤ hellingerGamma a b L ∧ hellingerGamma a b L ≤ 1 := by
  unfold hellingerGamma
  have hab : 0 < a + b := by linarith
  have h0 : 0 ≤ 2 * Real.sqrt (a * b) / (a + b) := by positivity
  have h1 : 2 * Real.sqrt (a * b) / (a + b) ≤ 1 := by
    rw [div_le_one hab]
    have hs := Real.sq_sqrt (mul_nonneg ha.le hb)
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha.le, Real.sq_sqrt hb,
      Real.sqrt_mul ha.le b, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  constructor
  · have := Real.rpow_le_one h0 h1 hL.le; linarith
  · have := Real.rpow_nonneg h0 L; linarith

end S69E

open Arxiv1504_01000 in
theorem solution (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L : ℝ)
    (hL : 0 < L) (φ : ℝ) (hφ : IsSelectedOA T L φ) :
    0 ≤ deltaH T L φ ∧ deltaH T L φ ≤ 1 := by
  have ha : ∀ l, 0 < (T l l).re := fun l => (Complex.pos_iff.mp (hT.diag_pos (i := l))).1
  have h1 := S69E.hg _ _ L (ha 1) (S69E.bnn T hT 1 φ) hL
  have h2 := S69E.hg _ _ L (ha 2) (S69E.bnn T hT 2 φ) hL
  unfold deltaH dH
  constructor
  · have := hφ.2; unfold dH at this; linarith
  · linarith [h1.1, h2.2]
