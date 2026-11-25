-- Prove2me | solution 1 for Arxiv1504_01000.oa_independent_of_looks
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:59:00.796877+00:00
-- url     : https://prove2.me/submissions/1ddb1999-aae9-4340-aeaa-a273b3f8e06f

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

lemma base_nn (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (l : Fin 3) (θ : ℝ) :
    0 ≤ 2 * Real.sqrt ((T l l).re * sigmaSq T l θ) / ((T l l).re + sigmaSq T l θ) := by
  have ha : 0 < (T l l).re := (Complex.pos_iff.mp (hT.diag_pos (i := l))).1
  have hb := bnn T hT l θ
  have : 0 < (T l l).re + sigmaSq T l θ := by linarith
  positivity

lemma dH_le_iff (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L L' : ℝ) (hL : 0 < L)
    (hL' : 0 < L') (l : Fin 3) (x y : ℝ) :
    dH T L l x ≤ dH T L l y ↔ dH T L' l x ≤ dH T L' l y := by
  unfold dH hellingerGamma
  have hx := base_nn T hT l x
  have hy := base_nn T hT l y
  rw [sub_le_sub_iff_left, sub_le_sub_iff_left, Real.rpow_le_rpow_iff hy hx hL,
    Real.rpow_le_rpow_iff hy hx hL']

lemma dH_lt_iff (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L L' : ℝ) (hL : 0 < L)
    (hL' : 0 < L') (x : ℝ) :
    dH T L 1 x < dH T L 2 x ↔ dH T L' 1 x < dH T L' 2 x := by
  unfold dH hellingerGamma
  have hx := base_nn T hT 1 x
  have hy := base_nn T hT 2 x
  rw [sub_lt_sub_iff_left, sub_lt_sub_iff_left, Real.rpow_lt_rpow_iff hy hx hL,
    Real.rpow_lt_rpow_iff hy hx hL']

lemma max_iff (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L L' : ℝ) (hL : 0 < L)
    (hL' : 0 < L') (l : Fin 3) (θ : ℝ) :
    IsMaxOn (dH T L l) oaRange θ ↔ IsMaxOn (dH T L' l) oaRange θ := by
  simp only [IsMaxOn, IsMaxFilter, Filter.eventually_principal]
  exact forall_congr' fun y => imp_congr_right fun _ => dH_le_iff T hT L L' hL hL' l y θ

end S69E

open Arxiv1504_01000 in
theorem solution (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.PosDef) (L L' : ℝ)
    (hL : 0 < L) (hL' : 0 < L') :
    (∀ θ, IsMaxOn (dH T L 2) oaRange θ ↔ IsMaxOn (dH T L' 2) oaRange θ) ∧
    (∀ θ, IsMaxOn (dH T L 1) oaRange θ ↔ IsMaxOn (dH T L' 1) oaRange θ) ∧
    (∀ φ, IsSelectedOA T L φ ↔ IsSelectedOA T L' φ) := by
  refine ⟨fun θ => S69E.max_iff T hT L L' hL hL' 2 θ, fun θ => S69E.max_iff T hT L L' hL hL' 1 θ,
    fun φ => ?_⟩
  unfold IsSelectedOA IsCandidateOA
  rw [S69E.dH_lt_iff T hT L L' hL hL' φ]
  simp only [S69E.max_iff T hT L L' hL hL']
