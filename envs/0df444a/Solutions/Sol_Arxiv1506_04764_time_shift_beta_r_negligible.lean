-- Prove2me | solution 1 for Arxiv1506_04764.time_shift_beta_r_negligible
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:47:59.540887+00:00
-- url     : https://prove2.me/submissions/921af077-09b7-4f02-9994-d02615d0ba06

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex
open Arxiv1506_04764

lemma dot_self_nonneg' (x : V3) : 0 ≤ dotProduct x x := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]

lemma len_sq (x : V3) : len x ^ 2 = dotProduct x x := by
  unfold len; rw [Real.sq_sqrt (dot_self_nonneg' x)]

lemma len_nonneg' (x : V3) : 0 ≤ len x := Real.sqrt_nonneg _

lemma cs3 (x y : V3) : (dotProduct x y) ^ 2 ≤ dotProduct x x * dotProduct y y := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0), sq_nonneg (x 0 * y 2 - x 2 * y 0),
    sq_nonneg (x 1 * y 2 - x 2 * y 1)]

lemma abs_dot_le (x y : V3) : |dotProduct x y| ≤ len x * len y := by
  apply abs_le_of_sq_le_sq' _ (mul_nonneg (len_nonneg' x) (len_nonneg' y)) |>.elim
    (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  rw [mul_pow, len_sq, len_sq]; exact cs3 x y

lemma len_pos_of_ne {x : V3} (hx : x ≠ 0) : 0 < len x := by
  unfold len
  apply Real.sqrt_pos.mpr
  rcases (dot_self_nonneg' x).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx
    have h' : dotProduct x x = 0 := h.symm
    simp only [dotProduct, Fin.sum_univ_three] at h'
    funext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- second-order expansion of the distance -/
lemma lin_dist (R d : V3) (hR : R ≠ 0) (hd : len d ≤ (1 / 2) * len R) :
    |len (R + d) - (len R + dotProduct (unitVec R) d)| ≤ 2 * len d ^ 2 / len R := by
  have hs := len_pos_of_ne hR
  set s := len R with hs_def
  set n := len d with hn_def
  set p := dotProduct R d with hp_def
  have hn0 : 0 ≤ n := len_nonneg' d
  have hp : |p| ≤ s * n := abs_dot_le R d
  have hu : dotProduct (unitVec R) d = p / s := by
    simp only [unitVec, smul_dotProduct, smul_eq_mul, hp_def]
    rw [← hs_def]; field_simp
  have hL2 : len (R + d) ^ 2 = s ^ 2 + 2 * p + n ^ 2 := by
    rw [len_sq, hs_def, hn_def, len_sq, len_sq, hp_def]
    simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply]; ring
  have hL0 : 0 ≤ len (R + d) := len_nonneg' _
  set L := len (R + d)
  rw [hu]
  have hpa := abs_le.mp hp
  have hm : s / 2 ≤ s + p / s := by
    have : -(s * n) / s ≤ p / s := div_le_div_of_nonneg_right hpa.1 hs.le
    rw [neg_div, mul_div_cancel_left₀ _ hs.ne'] at this
    linarith
  have hdiff : L ^ 2 - (s + p / s) ^ 2 = n ^ 2 - (p / s) ^ 2 := by
    rw [hL2]; field_simp; ring
  have hps : (p / s) ^ 2 ≤ n ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have := sq_le_sq' (by linarith [hpa.1]) hpa.2
    nlinarith
  have hge : s + p / s ≤ L := by
    by_contra h
    push Not at h
    nlinarith
  have hprod : (L - (s + p / s)) * (L + (s + p / s)) ≤ n ^ 2 := by
    nlinarith
  have hsum : s / 2 ≤ L + (s + p / s) := by linarith
  rw [abs_of_nonneg (by linarith), le_div_iff₀ hs]
  nlinarith

theorem solution (c vs x y h t' : ℝ)
    (hc : 0 < c) (hvs : 0 < vs) (hvc : vs < c) (ht' : 0 < t') :
    |dotProduct (betaVec c ![vs, 0, 0]) ![x, y, h] / c| =
        |x| / (vs * t') * ((vs / c) ^ 2 * t') ∧
      (dotProduct (betaVec c ![vs, 0, 0]) ![x, y, h] = 0 ↔ x = 0) := by
  have hd : dotProduct (betaVec c ![vs, 0, 0]) ![x, y, h] = vs * x / c := by
    simp [betaVec, dotProduct, Fin.sum_univ_three]; field_simp
  rw [hd]
  constructor
  · rw [abs_div, abs_div, abs_mul, abs_of_pos hvs, abs_of_pos hc]
    field_simp
  · constructor
    · intro h0
      have : vs * x = 0 := by
        rcases div_eq_zero_iff.mp h0 with h1 | h1
        · exact h1
        · exact absurd h1 hc.ne'
      exact (mul_eq_zero.mp this).resolve_left hvs.ne'
    · rintro rfl; simp

