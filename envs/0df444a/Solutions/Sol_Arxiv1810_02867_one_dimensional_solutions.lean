-- Prove2me | solution 1 for Arxiv1810_02867.one_dimensional_solutions
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:47:39.880809+00:00
-- url     : https://prove2.me/submissions/df7fc32c-18b8-4776-b4b7-1da8770bda4b

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71OD
open Arxiv1810_02867

lemma d1 (gamma m : ℝ) (F : ℝ → ℝ) (hF : Differentiable ℝ F) :
    D1g gamma (fun x t => F (t + m * x)) = fun x t => (m + gamma) * deriv F (t + m * x) := by
  funext x t
  unfold D1g
  have hx : HasDerivAt (fun y => F (t + m * y)) (deriv F (t + m * x) * m) x := by
    have h1 : HasDerivAt (fun y : ℝ => t + m * y) m x := by
      simpa using ((hasDerivAt_id x).const_mul m).const_add t
    exact (hF _).hasDerivAt.comp x h1
  have ht : HasDerivAt (fun s => F (s + m * x)) (deriv F (t + m * x) * 1) t := by
    have h1 : HasDerivAt (fun s : ℝ => s + m * x) 1 t := by
      simpa using (hasDerivAt_id t).add_const (m * x)
    exact (hF _).hasDerivAt.comp t h1
  rw [hx.deriv, ht.deriv]; ring

lemma dt (m x : ℝ) (F : ℝ → ℝ) (hF : Differentiable ℝ F) (hF' : Differentiable ℝ (deriv F))
    (t : ℝ) :
    deriv (fun s => deriv (fun s' => F (s' + m * x)) s) t = deriv (deriv F) (t + m * x) := by
  have e : (fun s => deriv (fun s' => F (s' + m * x)) s) = fun s => deriv F (s + m * x) := by
    funext s
    have h1 : HasDerivAt (fun s : ℝ => s + m * x) 1 s := by
      simpa using (hasDerivAt_id s).add_const (m * x)
    exact ((hF _).hasDerivAt.comp s h1).deriv.trans (mul_one _)
  rw [e]
  have h1 : HasDerivAt (fun s : ℝ => s + m * x) 1 t := by
    simpa using (hasDerivAt_id t).add_const (m * x)
  exact ((hF' _).hasDerivAt.comp t h1).deriv.trans (mul_one _)

lemma wave (gamma m ab : ℝ) (hm : (m + gamma) ^ 2 = ab) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) :
    ∀ x t, D1g gamma (D1g gamma (fun x t => F (t + m * x))) x t -
      ab * deriv (fun s => deriv (fun s' => (fun x t => F (t + m * x)) x s') s) t = 0 := by
  have h2 := contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) F from hF)
  have hF1 : Differentiable ℝ F := h2.1
  have hF2 : Differentiable ℝ (deriv F) := h2.2.2.differentiable (by norm_num)
  intro x t
  rw [d1 gamma m F hF1]
  have : (fun x t => (m + gamma) * deriv F (t + m * x)) =
      fun x t => (fun u => (m + gamma) * deriv F u) (t + m * x) := rfl
  rw [this, d1 gamma m _ (hF2.const_mul _)]
  simp only
  rw [dt m x F hF1 hF2 t, deriv_const_mul _ (hF2 _), ← hm]
  ring

end S71OD

open Arxiv1810_02867 S71OD in
theorem solution (alpha beta gamma : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : |gamma| < 1 / refVel alpha beta) (S : ℝ → ℝ) (hS : ContDiff ℝ 2 S) :
    (∀ (plus : Bool) (x t : ℝ),
      D1g gamma (D1g gamma (oneWay plus alpha beta gamma S)) x t -
        alpha * beta * deriv (fun s => deriv (fun s' => oneWay plus alpha beta gamma S x s') s) t
        = 0) ∧
    (∀ x t, oneWay true alpha beta gamma S x t =
      S (t - (1 + gamma * refVel alpha beta) / refVel alpha beta * x)) ∧
    (∀ x t, oneWay false alpha beta gamma S x t =
      S (t - (1 - gamma * refVel alpha beta) / refVel alpha beta * (-x))) ∧
    0 < (1 + gamma * refVel alpha beta) / refVel alpha beta ∧
    0 < (1 - gamma * refVel alpha beta) / refVel alpha beta := by
  have hab : 0 < alpha * beta := mul_pos halpha hbeta
  have hc : 0 < refVel alpha beta := Real.rpow_pos_of_pos hab _
  have hc2 : refVel alpha beta ^ 2 * (alpha * beta) = 1 := by
    unfold refVel
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  set c := refVel alpha beta with hcdef
  have hg := abs_lt.1 hgamma
  have hgc1 : -1 < gamma * c := by
    have h := mul_lt_mul_of_pos_right hg.1 hc
    rwa [neg_mul, one_div_mul_cancel hc.ne'] at h
  have hgc2 : gamma * c < 1 := by
    have := hg.2; rw [lt_div_iff₀ hc] at this; linarith
  have eT : oneWay true alpha beta gamma S = fun x t => S (t + (-((1 + gamma * c) / c)) * x) := by
    funext x t; simp only [oneWay, if_true, ← hcdef]; congr 1; field_simp; ring
  have eF : oneWay false alpha beta gamma S = fun x t => S (t + ((1 - gamma * c) / c) * x) := by
    funext x t; simp only [oneWay, Bool.false_eq_true, if_false, ← hcdef]; congr 1; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro plus x t
    cases plus
    · rw [eF]
      apply wave gamma _ (alpha * beta) _ S hS
      field_simp; nlinarith [hc2]
    · rw [eT]
      apply wave gamma _ (alpha * beta) _ S hS
      field_simp; nlinarith [hc2]
  · intro x t; rw [eT]; simp only; congr 1; ring
  · intro x t; rw [eF]; simp only; congr 1; ring
  · apply div_pos (by linarith) hc
  · apply div_pos (by linarith) hc
