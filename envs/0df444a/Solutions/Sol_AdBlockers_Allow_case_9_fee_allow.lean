-- Prove2me | solution 1 for AdBlockers.Allow.case_9_fee_allow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:36:27.887175+00:00
-- url     : https://prove2.me/submissions/1c2e457b-359a-4f28-8c5c-c1b6fff2e4bc

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

lemma ab_clip_le {t : ℝ} (ht : 0 ≤ t) : clip01 t ≤ t := by
  unfold clip01; exact max_le ht (min_le_right _ _)

lemma ab_clip_zero {t : ℝ} (ht : t ≤ 0) : clip01 t = 0 := by
  unfold clip01; exact max_eq_left (le_trans (min_le_right _ _) ht)

lemma ab_clip_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clip01 t = t := by
  unfold clip01; rw [min_eq_right h1, max_eq_right h0]

lemma ab_two_le (A B t1 t2 e V : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hboth : 0 ≤ t1 → 0 ≤ t2 → A * t1 * e + B * t2 * e ≤ V)
    (h1 : 0 ≤ t1 → t2 ≤ 0 → A * t1 * e ≤ V)
    (h2 : t1 ≤ 0 → 0 ≤ t2 → B * t2 * e ≤ V)
    (h0 : 0 ≤ V) : A * clip01 t1 * e + B * clip01 t2 * e ≤ V := by
  rcases le_total 0 t1 with ht1 | ht1 <;> rcases le_total 0 t2 with ht2 | ht2
  · have a1 := mul_le_mul_of_nonneg_right (ab_clip_le ht1) he
    have a2 := mul_le_mul_of_nonneg_right (ab_clip_le ht2) he
    have := hboth ht1 ht2
    nlinarith [mul_le_mul_of_nonneg_left a1 hA, mul_le_mul_of_nonneg_left a2 hB]
  · have a1 := mul_le_mul_of_nonneg_right (ab_clip_le ht1) he
    have := h1 ht1 ht2
    rw [ab_clip_zero ht2]
    nlinarith [mul_le_mul_of_nonneg_left a1 hA]
  · have a2 := mul_le_mul_of_nonneg_right (ab_clip_le ht2) he
    have := h2 ht1 ht2
    rw [ab_clip_zero ht1]
    nlinarith [mul_le_mul_of_nonneg_left a2 hB]
  · rw [ab_clip_zero ht1, ab_clip_zero ht2]; simpa using h0

lemma ab_one_le (A t e V : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e)
    (h1 : 0 ≤ t → A * t * e ≤ V) (h0 : 0 ≤ V) : A * clip01 t * e ≤ V := by
  rcases le_total 0 t with ht | ht
  · have a1 := mul_le_mul_of_nonneg_right (ab_clip_le ht) he
    have := h1 ht
    nlinarith [mul_le_mul_of_nonneg_left a1 hA]
  · rw [ab_clip_zero ht]; simpa using h0

lemma ab_quad (A B c1 c2 k1 k2 x e : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hk1 : 0 ≤ k1)
    (hk2 : 0 ≤ k2) (hfoc : A * c1 + B * c2 = 2 * (A * k1 + B * k2) * x) :
    A * ((c1 - k1 * e) / 2) * e + B * ((c2 - k2 * e) / 2) * e ≤
      A * ((c1 - k1 * x) / 2) * x + B * ((c2 - k2 * x) / 2) * x := by
  have h0 : A * c1 + B * c2 - 2 * (A * k1 + B * k2) * x = 0 := by linarith
  have hK : 0 ≤ A * k1 + B * k2 := add_nonneg (mul_nonneg hA hk1) (mul_nonneg hB hk2)
  have key : A * ((c1 - k1 * x) / 2) * x + B * ((c2 - k2 * x) / 2) * x -
      (A * ((c1 - k1 * e) / 2) * e + B * ((c2 - k2 * e) / 2) * e) =
      (A * k1 + B * k2) * (x - e) ^ 2 / 2 +
        (x - e) * (A * c1 + B * c2 - 2 * (A * k1 + B * k2) * x) / 2 := by ring
  rw [h0] at key
  nlinarith [mul_nonneg hK (sq_nonneg (x - e))]

lemma ab_fee_allow_NE (lam μ β γ p a : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hp : p * (3 * lam + 4 * μ) = 3 * lam + 2 * μ)
    (ha : β * a * (3 * lam + 4 * μ) = 3 * (lam + μ)) :
    IsStage2NE lam μ β γ .fee .allow p a ∧
      rev₁ lam μ β γ .fee .allow p a = (lam + μ) * p ^ 2 / 2 ∧
      rev₂ lam μ β γ .fee .allow p a = lam * β * a ^ 2 / 2 := by
  have hD : 0 < 3 * lam + 4 * μ := by linarith
  have hp0 : 0 < p := by nlinarith
  have hp1 : p < 1 := by nlinarith
  have hb0 : 0 < β * a := by nlinarith
  have hb1 : β * a < 1 := by nlinarith
  have ha0 : 0 < a := by
    by_contra h; have h := not_lt.mp h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ.le h]
  have h2ba : 2 * (β * a) = 1 + p := by
    apply mul_right_cancel₀ hD.ne'; linear_combination 2 * ha - hp
  have hfoc : lam * (1 + β * a) + μ * 1 = 2 * (lam * 1 + μ * 1) * p := by
    apply mul_right_cancel₀ hD.ne'; linear_combination lam * ha - 2 * (lam + μ) * hp
  have c1 : clip01 ((1 + β * a - p) / 2) = (1 + β * a - p) / 2 :=
    ab_clip_eq (by linarith) (by linarith)
  have c2 : clip01 ((1 + 0 - p) / 2) = (1 + 0 - p) / 2 := ab_clip_eq (by linarith) (by linarith)
  have c3 : clip01 ((1 + p - β * a) / 2) = (1 + p - β * a) / 2 :=
    ab_clip_eq (by linarith) (by linarith)
  refine ⟨⟨hp0.le, ha0.le, ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]
    rw [c1, c2]
    have hq := fun e => ab_quad lam μ (1 + β * a) 1 1 1 p e hlam.le hμ.le zero_le_one
      zero_le_one hfoc
    apply ab_two_le lam μ _ _ e _ hlam.le hμ.le he
    · intro _ _; have := hq e; simp only [one_mul] at this; linarith
    · intro _ ht2
      have := hq 1
      have hx : lam * ((1 + β * a - e) / 2) * e ≤ lam * ((1 + β * a - 1) / 2) * 1 := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ e - 1 by linarith) (show (0:ℝ) ≤ e - β * a by linarith)]
      simp only [one_mul] at this; nlinarith
    · intro ht1 ht2; exfalso; linarith
    · have : 0 ≤ (1 + β * a - p) / 2 := by linarith
      have : 0 ≤ (1 + 0 - p) / 2 := by linarith
      positivity
  · intro e he
    simp only [rev₂, rev₁, hotellingShare, disNon, disAdb, payAdb, mul_zero, add_zero]
    rw [c3]
    have hfoc2 : lam * (1 + p) + 0 * 0 = 2 * (lam * β + 0 * 0) * a := by linear_combination -lam * h2ba
    have := ab_quad lam 0 (1 + p) 0 β 0 a e hlam.le le_rfl hβ.le le_rfl hfoc2
    apply ab_one_le lam _ e _ hlam.le he
    · intro _; simp at this; linarith
    · have : 0 ≤ (1 + p - β * a) / 2 := by linarith
      positivity
  · simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]
    rw [c1, c2]; linear_combination (p / 2) * hfoc
  · simp only [rev₂, rev₁, hotellingShare, disNon, disAdb, payAdb, mul_zero, add_zero]
    rw [c3]; linear_combination (-lam * a / 2) * h2ba

end AdBlockers.Allow

open AdBlockers.Allow

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) :
    IsStage2NE lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
        (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) ∧
      rev₁ lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
          (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) =
        (lam + μ) * (3 * lam + 2 * μ) ^ 2 / (2 * (3 * lam + 4 * μ) ^ 2) ∧
      rev₂ lam μ β γ .fee .allow ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
          (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) =
        9 * lam * (lam + μ) ^ 2 / (2 * β * (3 * lam + 4 * μ) ^ 2) := by
  have hD : 0 < 3 * lam + 4 * μ := by linarith
  obtain ⟨h1, h2, h3⟩ := ab_fee_allow_NE lam μ β γ ((3 * lam + 2 * μ) / (3 * lam + 4 * μ))
    (3 * (lam + μ) / (β * (3 * lam + 4 * μ))) hlam hμ hβ (by field_simp) (by field_simp)
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; field_simp
  · rw [h3]; field_simp; ring
