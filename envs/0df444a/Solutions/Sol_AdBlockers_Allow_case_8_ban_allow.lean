-- Prove2me | solution 1 for AdBlockers.Allow.case_8_ban_allow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:44:52.21034+00:00
-- url     : https://prove2.me/submissions/06bde396-99ec-4f4c-91f9-f532f2c23c90

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


lemma ab_jump_norm (m s : ℝ) (hm : 0 < m) (hs : 0 ≤ s) (hS : 4 * s ≤ 4 * m + m ^ 2) :
    (6 + 6 * s + m) ^ 2 ≤ 4 * (1 + s) * (3 + 2 * m) ^ 2 := by
  have hSpos : 0 < m + m ^ 2 / 4 := by positivity
  have hSs : 0 ≤ m + m ^ 2 / 4 - s := by linarith
  have P0 : 0 ≤ 36 * m + 15 * m ^ 2 := by positivity
  have PS : 0 ≤ m ^ 2 * (12 + 14 * m + 7 / 2 * m ^ 2) / 2 := by positivity
  have key : (m + m ^ 2 / 4) * (4 * (1 + s) * (3 + 2 * m) ^ 2 - (6 + 6 * s + m) ^ 2) =
      (m + m ^ 2 / 4 - s) * (36 * m + 15 * m ^ 2) + s * (m ^ 2 * (12 + 14 * m + 7 / 2 * m ^ 2) / 2)
        + 36 * s * (m + m ^ 2 / 4 - s) * (m + m ^ 2 / 4) := by ring
  have : 0 ≤ (m + m ^ 2 / 4) * (4 * (1 + s) * (3 + 2 * m) ^ 2 - (6 + 6 * s + m) ^ 2) := by
    rw [key]
    have := mul_nonneg hSs P0
    have := mul_nonneg hs PS
    have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 36) hs) hSs) hSpos.le
    linarith
  by_contra hc
  have hc : 4 * (1 + s) * (3 + 2 * m) ^ 2 - (6 + 6 * s + m) ^ 2 < 0 := by linarith
  have := mul_neg_of_pos_of_neg hSpos hc
  linarith

lemma ab_jump (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (hreg : 4 * γ * lam ≤ (4 * lam + μ) * β) :
    lam * (6 * β * lam + 6 * γ * μ + β * μ) ^ 2 ≤
      4 * β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 := by
  have h := ab_jump_norm (μ / lam) (γ * μ / (β * lam)) (by positivity) (by positivity) (by
    have key : 4 * (μ / lam) + (μ / lam) ^ 2 - 4 * (γ * μ / (β * lam)) =
        μ * ((4 * lam + μ) * β - 4 * γ * lam) / (β * lam ^ 2) := by field_simp; try ring
    have : 0 ≤ μ * ((4 * lam + μ) * β - 4 * γ * lam) / (β * lam ^ 2) :=
      div_nonneg (mul_nonneg hμ.le (by linarith)) (by positivity)
    linarith)
  have e1 : (6 + 6 * (γ * μ / (β * lam)) + μ / lam) ^ 2 =
      (6 * β * lam + 6 * γ * μ + β * μ) ^ 2 / (β * lam) ^ 2 := by field_simp
  have e2 : 4 * (1 + γ * μ / (β * lam)) * (3 + 2 * (μ / lam)) ^ 2 =
      4 * β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 / (lam * (β * lam) ^ 2) := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)] at h
  have : lam * (6 * β * lam + 6 * γ * μ + β * μ) ^ 2 * (β * lam) ^ 2 ≤
      4 * β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 * (β * lam) ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

lemma ab_banallow_II (lam μ β γ x : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (hx : β * x = 1) (hreg : (4 * lam + μ) * β ≤ 4 * γ * lam) :
    IsStage2NE lam μ β γ .ban .allow x x ∧ rev₁ lam μ β γ .ban .allow x x = lam / (2 * β) := by
  have hx0 : 0 < x := by
    by_contra h; have h := le_of_not_gt h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ.le h]
  have hxb : x = 1 / β := by field_simp; linarith
  have hγβ : β ≤ γ := by nlinarith
  have hγx : 1 ≤ γ * x := by nlinarith
  have c1 : clip01 ((1 + β * x - β * x) / 2) = 1 / 2 := by
    rw [show (1 + β * x - β * x) / 2 = 1 / 2 by ring]; exact ab_clip_eq (by norm_num) (by norm_num)
  have c2 : clip01 ((1 + 0 - γ * x) / 2) = 0 := ab_clip_zero (by linarith)
  have hV : lam * x / 2 = lam / (2 * β) := by rw [hxb]; field_simp
  have hR : rev₁ lam μ β γ .ban .allow x x = lam * x / 2 := by
    simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]; rw [c1, c2]; ring
  refine ⟨⟨hx0.le, hx0.le, ?_, ?_⟩, by rw [hR, hV]⟩
  · intro e he
    rw [hR]
    simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]
    apply ab_two_le lam μ _ _ e _ hlam.le hμ.le he
    · intro _ _
      rw [hV, le_div_iff₀ (by positivity), hx]
      nlinarith [sq_nonneg (lam * (1 - β * e) - μ * (β * e) / 2),
        mul_nonneg (sub_nonneg.2 hreg) (mul_nonneg (mul_nonneg hμ.le hβ.le) (sq_nonneg e))]
    · intro _ _
      rw [hV, le_div_iff₀ (by positivity), hx]
      nlinarith [mul_nonneg hlam.le (sq_nonneg (1 - β * e))]
    · intro h1 h2; exfalso; nlinarith
    · positivity
  · intro e he
    simp only [rev₂, rev₁, hotellingShare, disNon, disAdb, payAdb, mul_zero, add_zero]
    rw [c1]
    apply ab_one_le lam _ e _ hlam.le he
    · intro _
      have : lam * (1 / 2) * x = lam / (2 * β) := by rw [← hV]; ring
      rw [this, le_div_iff₀ (by positivity), hx]
      nlinarith [mul_nonneg hlam.le (sq_nonneg (1 - β * e))]
    · positivity

lemma ab_banallow_I (lam μ β γ A1 A2 : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hγ : 0 < γ) (hreg : 4 * γ * lam < (4 * lam + μ) * β)
    (h2 : β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 ≤ lam * (3 * β * lam + 4 * γ * μ) ^ 2)
    (hA1 : A1 * (3 * β * lam + 4 * γ * μ) = 3 * lam + 2 * μ) (hA2 : 2 * β * A2 = 1 + β * A1) :
    IsStage2NE lam μ β γ .ban .allow A1 A2 ∧ rev₁ lam μ β γ .ban .allow A1 A2 ≤ lam / (2 * β) := by
  have hEp : 0 < 3 * β * lam + 4 * γ * μ := by positivity
  have hNp : 0 < 3 * lam + 2 * μ := by positivity
  have hA1p : 0 < A1 := by
    by_contra h; have h := le_of_not_gt h
    have := mul_nonpos_of_nonpos_of_nonneg h hEp.le
    linarith
  have hsq : (β * (3 * lam + 2 * μ)) ^ 2 ≤ (3 * β * lam + 4 * γ * μ) ^ 2 := by
    have h3 : 0 ≤ β * γ * μ * (3 * lam + 2 * μ) ^ 2 := by positivity
    have : lam * (β * (3 * lam + 2 * μ)) ^ 2 ≤ lam * (3 * β * lam + 4 * γ * μ) ^ 2 := by
      have e : β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 =
          lam * (β * (3 * lam + 2 * μ)) ^ 2 + β * γ * μ * (3 * lam + 2 * μ) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left this hlam
  have hβN : β * (3 * lam + 2 * μ) ≤ 3 * β * lam + 4 * γ * μ :=
    (sq_le_sq₀ (by positivity) hEp.le).1 hsq
  have hγβ : β ≤ 2 * γ := by
    have : 2 * β * μ ≤ 4 * γ * μ := by linarith
    nlinarith
  have hβA1 : β * A1 ≤ 1 := by
    have : β * A1 * (3 * β * lam + 4 * γ * μ) ≤ 1 * (3 * β * lam + 4 * γ * μ) := by
      have e : β * A1 * (3 * β * lam + 4 * γ * μ) = β * (A1 * (3 * β * lam + 4 * γ * μ)) := by ring
      rw [e, hA1]; linarith
    exact le_of_mul_le_mul_right this hEp
  have hγA1 : γ * A1 ≤ 1 := by
    have hγN : γ * (3 * lam + 2 * μ) ≤ 3 * β * lam + 4 * γ * μ := by
      have h4 : 4 * lam * (γ * (3 * lam + 2 * μ)) ≤ 4 * lam * (3 * β * lam + 4 * γ * μ) := by
        have e1 : 4 * lam * (γ * (3 * lam + 2 * μ)) = 3 * lam * (4 * γ * lam) + 8 * γ * lam * μ := by
          ring
        have e2 : 4 * lam * (3 * β * lam + 4 * γ * μ) =
            3 * lam * ((4 * lam + μ) * β) + lam * μ * (16 * γ - 3 * β) := by ring
        have i1 : 3 * lam * (4 * γ * lam) ≤ 3 * lam * ((4 * lam + μ) * β) :=
          mul_le_mul_of_nonneg_left hreg.le (by positivity)
        have i2 : 8 * γ * lam * μ ≤ lam * μ * (16 * γ - 3 * β) := by
          have : 0 ≤ lam * μ * (8 * γ - 3 * β) := mul_nonneg (by positivity) (by linarith)
          nlinarith
        linarith
      exact le_of_mul_le_mul_left h4 (by positivity)
    have : γ * A1 * (3 * β * lam + 4 * γ * μ) ≤ 1 * (3 * β * lam + 4 * γ * μ) := by
      have e : γ * A1 * (3 * β * lam + 4 * γ * μ) = γ * (A1 * (3 * β * lam + 4 * γ * μ)) := by ring
      rw [e, hA1]; linarith
    exact le_of_mul_le_mul_right this hEp
  have hbA1 : 0 < β * A1 := mul_pos hβ hA1p
  have hgA1 : 0 < γ * A1 := mul_pos hγ hA1p
  have hA2p : 0 < A2 := by
    by_contra h; have h := le_of_not_gt h
    have := mul_nonpos_of_nonneg_of_nonpos hβ.le h
    linarith
  have hfoc : lam * (1 + β * A2) + μ * 1 = 2 * (lam * β + μ * γ) * A1 := by
    linear_combination (lam / 2) * hA2 - (1 / 2) * hA1
  have c1 : clip01 ((1 + β * A2 - β * A1) / 2) = (1 + β * A2 - β * A1) / 2 :=
    ab_clip_eq (by linarith) (by linarith)
  have c2 : clip01 ((1 + 0 - γ * A1) / 2) = (1 + 0 - γ * A1) / 2 :=
    ab_clip_eq (by linarith) (by linarith)
  have c3 : clip01 ((1 + β * A1 - β * A2) / 2) = (1 + β * A1 - β * A2) / 2 :=
    ab_clip_eq (by linarith) (by linarith)
  have hq := fun e => ab_quad lam μ (1 + β * A2) 1 β γ A1 e hlam.le hμ.le hβ.le hγ.le hfoc
  have hVeq : lam * ((1 + β * A2 - β * A1) / 2) * A1 + μ * ((1 - γ * A1) / 2) * A1 =
      (β * lam + γ * μ) * A1 ^ 2 / 2 := by
    linear_combination A1 / 2 * hfoc
  have hV0 : 0 ≤ (β * lam + γ * μ) * A1 ^ 2 / 2 := by positivity
  have hR : rev₁ lam μ β γ .ban .allow A1 A2 = (β * lam + γ * μ) * A1 ^ 2 / 2 := by
    simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]; rw [c1, c2, ← hVeq]; ring
  have hjump : lam * (1 + β * A2) ^ 2 ≤ 8 * β * ((β * lam + γ * μ) * A1 ^ 2 / 2) := by
    have J := ab_jump lam μ β γ hlam hμ hβ hγ hreg.le
    have e1 : (1 + β * A2) * (3 * β * lam + 4 * γ * μ) = 6 * β * lam + 6 * γ * μ + β * μ := by
      linear_combination (3 * β * lam + 4 * γ * μ) / 2 * hA2 + β / 2 * hA1
    have : lam * (1 + β * A2) ^ 2 * (3 * β * lam + 4 * γ * μ) ^ 2 ≤
        8 * β * ((β * lam + γ * μ) * A1 ^ 2 / 2) * (3 * β * lam + 4 * γ * μ) ^ 2 := by
      have e2 : lam * (1 + β * A2) ^ 2 * (3 * β * lam + 4 * γ * μ) ^ 2 =
          lam * ((1 + β * A2) * (3 * β * lam + 4 * γ * μ)) ^ 2 := by ring
      have e3 : 8 * β * ((β * lam + γ * μ) * A1 ^ 2 / 2) * (3 * β * lam + 4 * γ * μ) ^ 2 =
          4 * β * (β * lam + γ * μ) * (A1 * (3 * β * lam + 4 * γ * μ)) ^ 2 := by ring
      rw [e2, e3, hA1, e1]; exact J
    exact le_of_mul_le_mul_right this (by positivity)
  refine ⟨⟨hA1p.le, hA2p.le, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [hR]
    simp only [rev₁, hotellingShare, disNon, disAdb, payAdb]
    apply ab_two_le lam μ _ _ e _ hlam.le hμ.le he
    · intro _ _
      have := hq e
      have e' : (1 + 0 - γ * e) = (1 - γ * e) := by ring
      rw [e']; linarith
    · intro _ _
      have hsq' : 0 ≤ lam * (1 + β * A2 - 2 * β * e) ^ 2 := by positivity
      have e2 : lam * (1 + β * A2) ^ 2 - 8 * β * (lam * ((1 + β * A2 - β * e) / 2) * e) =
          lam * (1 + β * A2 - 2 * β * e) ^ 2 := by ring
      have : 8 * β * (lam * ((1 + β * A2 - β * e) / 2) * e) ≤
          8 * β * ((β * lam + γ * μ) * A1 ^ 2 / 2) := by linarith
      exact le_of_mul_le_mul_left this (by positivity)
    · intro ht1 ht2
      have hbc : β * ((1 + β * A2) / β) = 1 + β * A2 := by field_simp
      have hec : (1 + β * A2) / β ≤ e := by
        have : β * ((1 + β * A2) / β) ≤ β * e := by linarith
        exact le_of_mul_le_mul_left this hβ
      have hc0 : 0 ≤ (1 + β * A2) / β := by positivity
      have hc3 : 3 ≤ 2 * (β * ((1 + β * A2) / β)) := by rw [hbc]; linarith
      have hγc : 3 ≤ 4 * (γ * ((1 + β * A2) / β)) := by
        have := mul_le_mul_of_nonneg_right hγβ hc0
        linarith
      have hγe : γ * ((1 + β * A2) / β) ≤ γ * e := mul_le_mul_of_nonneg_left hec hγ.le
      have := hq ((1 + β * A2) / β)
      rw [hbc, show (1 + β * A2 - (1 + β * A2)) / 2 = 0 by ring] at this
      have hp := mul_nonneg (mul_nonneg hμ.le (sub_nonneg.2 hec))
        (by linarith : (0:ℝ) ≤ γ * e + γ * ((1 + β * A2) / β) - 1)
      have e3 : μ * ((1 + 0 - γ * e) / 2) * e -
          μ * ((1 - γ * ((1 + β * A2) / β)) / 2) * ((1 + β * A2) / β) =
          -(μ * (e - (1 + β * A2) / β) * (γ * e + γ * ((1 + β * A2) / β) - 1)) / 2 := by ring
      have e4 : lam * 0 * ((1 + β * A2) / β) = 0 := by ring
      linarith
    · exact hV0
  · intro e he
    simp only [rev₂, rev₁, hotellingShare, disNon, disAdb, payAdb, mul_zero, add_zero]
    rw [c3]
    have hfoc2 : lam * (1 + β * A1) + 0 * 0 = 2 * (lam * β + 0 * 0) * A2 := by
      linear_combination -lam * hA2
    have := ab_quad lam 0 (1 + β * A1) 0 β 0 A2 e hlam.le le_rfl hβ.le le_rfl hfoc2
    apply ab_one_le lam _ e _ hlam.le he
    · intro _; simp only [zero_mul, add_zero, zero_sub, mul_zero] at this; linarith
    · have : 0 ≤ (1 + β * A1 - β * A2) / 2 := by linarith
      positivity
  · rw [hR, le_div_iff₀ (by positivity)]
    have : (β * lam + γ * μ) * A1 ^ 2 / 2 * (2 * β) * (3 * β * lam + 4 * γ * μ) ^ 2 ≤
        lam * (3 * β * lam + 4 * γ * μ) ^ 2 := by
      have e3 : (β * lam + γ * μ) * A1 ^ 2 / 2 * (2 * β) * (3 * β * lam + 4 * γ * μ) ^ 2 =
          β * (β * lam + γ * μ) * (A1 * (3 * β * lam + 4 * γ * μ)) ^ 2 := by ring
      rw [e3, hA1]; exact h2
    exact le_of_mul_le_mul_right this (by positivity)

lemma ab_case8 (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (h2 : (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) :
    ∃ e₁ e₂ : ℝ, IsStage2NE lam μ β γ .ban .allow e₁ e₂ ∧
      rev₁ lam μ β γ .ban .allow e₁ e₂ ≤ lam / (2 * β) := by
  have h2' : β * (β * lam + γ * μ) * (3 * lam + 2 * μ) ^ 2 ≤
      lam * (3 * β * lam + 4 * γ * μ) ^ 2 := by
    have e : (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 =
        β * (β * lam + γ * μ) / (3 * β * lam + 4 * γ * μ) ^ 2 := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)] at h2
    linarith
  rcases le_or_gt ((4 * lam + μ) * β) (4 * γ * lam) with hreg | hreg
  · refine ⟨1 / β, 1 / β, ?_⟩
    obtain ⟨h, hr⟩ := ab_banallow_II lam μ β γ (1 / β) hlam hμ hβ hγ (by field_simp) hreg
    exact ⟨h, hr.le⟩
  · have hE : 0 < 3 * β * lam + 4 * γ * μ := by positivity
    set A1 := (3 * lam + 2 * μ) / (3 * β * lam + 4 * γ * μ) with hA1d
    refine ⟨A1, (1 + β * A1) / (2 * β), ?_⟩
    exact ab_banallow_I lam μ β γ A1 ((1 + β * A1) / (2 * β)) hlam hμ hβ hγ hreg h2'
      (by rw [hA1d]; field_simp) (by field_simp)

end AdBlockers.Allow

open AdBlockers.Allow

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (h2 : (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) :
    ∃ e₁ e₂ : ℝ, IsStage2NE lam μ β γ .ban .allow e₁ e₂ ∧
      rev₁ lam μ β γ .ban .allow e₁ e₂ ≤ lam / (2 * β) :=
  ab_case8 lam μ β γ hlam hμ hβ hγ h2
