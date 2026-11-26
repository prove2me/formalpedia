-- Prove2me | solution 1 for Arxiv2405_15536.kappa_objective_robust
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:59:01.628516+00:00
-- url     : https://prove2.me/submissions/27a59339-d308-4ceb-a9cf-5b53f72e7c5d

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

set_option autoImplicit false

open MeasureTheory Filter

namespace S73KF
open Arxiv2405_15536

lemma loss_eq (κ : ℝ) (hκ : κ ≠ 0) :
    lossKappa κ = fun ε => -(1 / κ) * Real.arsinh (κ * (-betaKappa κ * ε ^ 2)) := by
  funext ε
  unfold lossKappa expKappa
  rw [if_neg hκ]
  set y := -betaKappa κ * ε ^ 2
  have hb : 0 < Real.sqrt (1 + κ ^ 2 * y ^ 2) + κ * y := by
    have h1 : |κ * y| < Real.sqrt (1 + κ ^ 2 * y ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_lt_sqrt (sq_nonneg _)
      nlinarith
    have := neg_abs_le (κ * y)
    linarith
  rw [Real.log_rpow hb, Real.arsinh]
  congr 2
  rw [add_comm]; congr 2; ring

end S73KF

namespace S73KF
open Arxiv2405_15536
theorem infl :
    (∀ κ : ℝ, 0 < κ → κ < 2 / 3 → ∀ ε : ℝ, HasDerivAt (lossKappa κ)
      (2 * betaKappa κ * ε / Real.sqrt (1 + κ ^ 2 * betaKappa κ ^ 2 * ε ^ 4)) ε) ∧
    (∀ ε : ℝ, HasDerivAt (lossKappa 0) ε ε) := by
  constructor
  · intro κ hκ _ ε
    rw [loss_eq κ hκ.ne']
    set b := betaKappa κ
    have h1 : HasDerivAt (fun ε : ℝ => κ * (-b * ε ^ 2)) (κ * (-b * (2 * ε))) ε := by
      have := ((hasDerivAt_pow 2 ε).const_mul (-b)).const_mul κ
      simpa using this
    have h2 := (h1.arsinh).const_mul (-(1 / κ))
    refine h2.congr_deriv ?_
    have e : 1 + (κ * (-b * ε ^ 2)) ^ 2 = 1 + κ ^ 2 * b ^ 2 * ε ^ 4 := by ring
    rw [e, smul_eq_mul]
    have hs : 0 < Real.sqrt (1 + κ ^ 2 * b ^ 2 * ε ^ 4) := Real.sqrt_pos.2 (by positivity)
    field_simp
  · intro ε
    have hl : lossKappa 0 = fun ε => (1 / 2) * ε ^ 2 := by
      funext ε
      unfold lossKappa expKappa betaKappa
      simp only [if_true, Real.log_exp]
      ring
    rw [hl]
    have := (hasDerivAt_pow 2 ε).const_mul (1 / 2 : ℝ)
    refine this.congr_deriv ?_
    push_cast; ring

end S73KF

namespace S73KR
open Arxiv2405_15536

lemma beta_pos (κ : ℝ) (h0 : 0 < κ) (hκ : κ < 2 / 3) : 0 < betaKappa κ := by
  have h : κ ≠ 0 := h0.ne'
  have ha : 0 < |κ| := abs_pos.2 h
  have hk : |κ| < 2 / 3 := by rw [abs_of_pos h0]; exact hκ
  have h2 : |2 * κ| = 2 * |κ| := by rw [abs_mul]; norm_num
  have hA : 3 / 4 < 1 / |2 * κ| := by
    rw [h2, lt_div_iff₀ (by positivity)]; nlinarith
  unfold betaKappa
  rw [if_neg h]
  have g1 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 3 / 4 by linarith)
  have g2 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 1 / 4 by linarith)
  have g3 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| + 3 / 4 by linarith)
  have g4 := Real.Gamma_pos_of_pos (show 0 < 1 / |2 * κ| - 1 / 4 by linarith)
  have : 0 < |2 * κ| := by rw [h2]; positivity
  positivity

lemma tend (κ b : ℝ) (hκ : 0 < κ) (hb : 0 < b) (l : Filter ℝ)
    (hl : Tendsto (fun ε : ℝ => |ε|) l atTop) :
    Tendsto (fun ε => 2 * b * ε / Real.sqrt (1 + κ ^ 2 * b ^ 2 * ε ^ 4)) l (nhds 0) := by
  have ha : Tendsto (fun ε : ℝ => 2 / (κ * |ε|)) l (nhds 0) :=
    tendsto_const_nhds.div_atTop (hl.const_mul_atTop hκ)
  refine squeeze_zero_norm' ?_ ha
  filter_upwards [hl.eventually_gt_atTop 0] with ε hε
  have he : 0 < κ * b * ε ^ 2 := by
    have : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    rw [this]; positivity
  have hs : κ * b * ε ^ 2 ≤ Real.sqrt (1 + κ ^ 2 * b ^ 2 * ε ^ 4) := by
    have h2 : (κ * b * ε ^ 2) ^ 2 ≤ 1 + κ ^ 2 * b ^ 2 * ε ^ 4 := by nlinarith
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq he.le] at this
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le he hs), abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hb]
  calc 2 * b * |ε| / Real.sqrt (1 + κ ^ 2 * b ^ 2 * ε ^ 4) ≤ 2 * b * |ε| / (κ * b * ε ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) he hs
    _ = 2 / (κ * |ε|) := by
        rw [← sq_abs ε]; field_simp

end S73KR

open Arxiv2405_15536 S73KF S73KR in
theorem solution :
    (∀ κ : ℝ, 0 < κ → κ < 2 / 3 → IsRobust (influence κ)) ∧ IsNonRobust (influence 0) := by
  obtain ⟨h1, h0⟩ := infl
  constructor
  · intro κ hκ hκ'
    have e : influence κ = fun ε => 2 * betaKappa κ * ε / Real.sqrt (1 + κ ^ 2 * betaKappa κ ^ 2 * ε ^ 4) := by
      funext ε; exact (h1 κ hκ hκ' ε).deriv
    rw [e]
    have hb := beta_pos κ hκ hκ'
    exact ⟨tend κ _ hκ hb atTop tendsto_abs_atTop_atTop, tend κ _ hκ hb atBot tendsto_abs_atBot_atTop⟩
  · have e : influence 0 = fun ε => ε := by
      funext ε; exact (h0 ε).deriv
    rw [e]
    exact ⟨tendsto_id, tendsto_id⟩
