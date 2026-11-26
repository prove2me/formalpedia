-- Prove2me | solution 1 for Arxiv2405_15536.kappa_objective_max_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:55:15.391322+00:00
-- url     : https://prove2.me/submissions/d2e35fe7-f780-41fe-ac27-d7d9c0410f2f

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

set_option autoImplicit false

open MeasureTheory Filter

namespace S73ML
open Arxiv2405_15536

lemma exp_pos (κ y : ℝ) : 0 < expKappa κ y := by
  unfold expKappa
  split_ifs with h
  · exact Real.exp_pos y
  · apply Real.rpow_pos_of_pos
    have h1 : |κ * y| < Real.sqrt (1 + κ ^ 2 * y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      nlinarith
    have := neg_abs_le (κ * y)
    linarith

lemma z_pos (κ : ℝ) (hκ : |κ| < 2 / 3) : 0 < zKappa κ := by
  unfold zKappa
  split_ifs with h
  · positivity
  · have ha : 0 < |κ| := abs_pos.2 h
    have h2 : |2 * κ| = 2 * |κ| := by rw [abs_mul]; norm_num
    have hA : 3 / 4 < 1 / |2 * κ| := by
      rw [h2, lt_div_iff₀ (by positivity)]; nlinarith
    have hb : 0 < betaKappa κ := by
      unfold betaKappa
      rw [if_neg h]
      have g1 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 3 / 4 by linarith)
      have g2 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 1 / 4 by linarith)
      have g3 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 3 / 4 by linarith)
      have g4 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 1 / 4 by linarith)
      have : 0 < |2 * κ| := by rw [h2]; positivity
      positivity
    have g2 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 1 / 4 by linarith)
    have g4 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 1 / 4 by linarith)
    have h3 : 0 < Real.sqrt (Real.pi / betaKappa κ) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
    have h4 : 0 < |2 * κ| := by rw [h2]; positivity
    have h5 : 0 < |2 * κ| ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos h4 _
    positivity

end S73ML

open Arxiv2405_15536 S73ML in
theorem solution {M I : Type*} [Fintype I] (κ : ℝ) (hκ : |κ| < 2 / 3)
    (ε : M → I → ℝ) :
    (∀ m : M, -Real.log (kappaLikelihood κ (ε m)) =
      (Fintype.card I : ℝ) * Real.log (zKappa κ) + ∑ i, lossKappa κ (ε m i)) ∧
    (∀ m : M, (∀ m' : M, ∑ i, lossKappa κ (ε m i) ≤ ∑ i, lossKappa κ (ε m' i)) ↔
      (∀ m' : M, kappaLikelihood κ (ε m') ≤ kappaLikelihood κ (ε m))) := by
  have hZ := z_pos κ hκ
  have hL : ∀ m, 0 < kappaLikelihood κ (ε m) := by
    intro m; unfold kappaLikelihood kappaGaussian
    exact Finset.prod_pos (fun i _ => div_pos (exp_pos _ _) hZ)
  have h1 : ∀ m : M, -Real.log (kappaLikelihood κ (ε m)) =
      (Fintype.card I : ℝ) * Real.log (zKappa κ) + ∑ i, lossKappa κ (ε m i) := by
    intro m
    unfold kappaLikelihood kappaGaussian lossKappa
    rw [Real.log_prod (fun i _ => (div_pos (exp_pos _ _) hZ).ne')]
    simp only [Real.log_div (exp_pos _ _).ne' hZ.ne']
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_neg_distrib]
    ring
  refine ⟨h1, fun m => ?_⟩
  have key : ∀ m', (∑ i, lossKappa κ (ε m i) ≤ ∑ i, lossKappa κ (ε m' i) ↔
      kappaLikelihood κ (ε m') ≤ kappaLikelihood κ (ε m)) := by
    intro m'
    rw [← Real.log_le_log_iff (hL m') (hL m)]
    have a := h1 m; have b := h1 m'
    constructor <;> intro h <;> linarith
  exact forall_congr' key
