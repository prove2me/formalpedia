-- Prove2me | solution 1 for AdBlockers.Allow.case_2_fee_fee
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:37:16.800024+00:00
-- url     : https://prove2.me/submissions/9a95796e-7901-49ed-bcd1-70c2b1ee01b9

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

lemma ab_clip_pos {t : ℝ} (ht : 0 < t) : 0 < clip01 t := by
  unfold clip01; exact lt_max_of_lt_right (lt_min one_pos ht)

lemma ab_foc_aux (D k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ)
    (h : ∀ t, 0 < t → t < δ → t * (D - k * t) ≤ 0) : D ≤ 0 := by
  by_contra hD
  have hD : 0 < D := lt_of_not_ge hD
  set t := min δ (D / k) / 2 with ht
  have hm : 0 < min δ (D / k) := lt_min hδ (div_pos hD hk)
  have ht0 : 0 < t := by positivity
  have htδ : t < δ := by have := min_le_left δ (D / k); linarith
  have htD : k * t < D := by
    have := min_le_right δ (D / k)
    have h2 : k * (D / k) = D := by field_simp
    have : k * min δ (D / k) ≤ D := by nlinarith
    nlinarith
  have := h t ht0 htδ
  nlinarith [mul_pos ht0 (sub_pos.mpr htD)]

/-- positivity of the equilibrium share -/
lemma ab_share_pos (W k x y : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ e z, F e z = W * clip01 ((1 + k * z - k * e) / 2) * e) (hW : 0 < W) (hk : 0 < k)
    (hy : 0 ≤ y) (h : ∀ e, 0 ≤ e → F e y ≤ F x y) : 0 < (1 + k * y - k * x) / 2 := by
  by_contra hs
  have hs : (1 + k * y - k * x) / 2 ≤ 0 := le_of_not_gt hs
  have h0 : F x y = 0 := by rw [hF, ab_clip_zero hs]; ring
  have he : 0 < 1 / (2 * k) := by positivity
  have hkk : k * (1 / (2 * k)) = 1 / 2 := by field_simp
  have hpos : 0 < (1 + k * y - k * (1 / (2 * k))) / 2 := by rw [hkk]; nlinarith
  have := h (1 / (2 * k)) he.le
  rw [h0, hF] at this
  have := mul_pos (mul_pos hW (ab_clip_pos hpos)) he
  linarith

/-- first-order condition at an interior equilibrium share -/
lemma ab_br_foc (W k x y : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ e z, F e z = W * clip01 ((1 + k * z - k * e) / 2) * e) (hW : 0 < W) (hk : 0 < k)
    (hx : 0 ≤ x) (h : ∀ e, 0 ≤ e → F e y ≤ F x y)
    (hs0 : 0 < (1 + k * y - k * x) / 2) (hs1 : (1 + k * y - k * x) / 2 < 1) :
    2 * k * x = 1 + k * y := by
  have hFx : F x y = W * ((1 + k * y - k * x) / 2) * x := by
    rw [hF, ab_clip_eq hs0.le hs1.le]
  -- upward deviations
  have hup : (1 + k * y - 2 * k * x) ≤ 0 := by
    apply ab_foc_aux _ k ((1 + k * y - k * x) / k) hk (div_pos (by linarith) hk)
    intro t ht0 htδ
    have hkt : k * t < 1 + k * y - k * x := by
      have : k * t < k * ((1 + k * y - k * x) / k) := mul_lt_mul_of_pos_left htδ hk
      rwa [mul_div_cancel₀ _ hk.ne'] at this
    have := h (x + t) (by linarith)
    rw [hF, hFx, ab_clip_eq (by nlinarith) (by nlinarith)] at this
    have key : W * ((1 + k * y - k * (x + t)) / 2) * (x + t) - W * ((1 + k * y - k * x) / 2) * x
        = W / 2 * (t * (1 + k * y - 2 * k * x - k * t)) := by ring
    have : W / 2 * (t * (1 + k * y - 2 * k * x - k * t)) ≤ 0 := by linarith
    by_contra hc
    have := mul_pos (half_pos hW) (lt_of_not_ge hc)
    linarith
  -- downward deviations
  have hdown : -(1 + k * y - 2 * k * x) ≤ 0 := by
    rcases eq_or_lt_of_le hx with hx0 | hx0
    · subst hx0; nlinarith
    apply ab_foc_aux _ k (min x ((1 - k * y + k * x) / k)) hk
      (lt_min hx0 (by apply div_pos _ hk; linarith))
    intro t ht0 htδ
    have htx : t < x := lt_of_lt_of_le htδ (min_le_left _ _)
    have ht2 : t < (1 - k * y + k * x) / k := lt_of_lt_of_le htδ (min_le_right _ _)
    have hkt : k * t < 1 - k * y + k * x := by
      have : k * t < k * ((1 - k * y + k * x) / k) := mul_lt_mul_of_pos_left ht2 hk
      rwa [mul_div_cancel₀ _ hk.ne'] at this
    have := h (x - t) (by linarith)
    rw [hF, hFx, ab_clip_eq (by nlinarith) (by nlinarith)] at this
    have key : W * ((1 + k * y - k * (x - t)) / 2) * (x - t) - W * ((1 + k * y - k * x) / 2) * x
        = W / 2 * (t * (-(1 + k * y - 2 * k * x) - k * t)) := by ring
    have : W / 2 * (t * (-(1 + k * y - 2 * k * x) - k * t)) ≤ 0 := by linarith
    by_contra hc
    have := mul_pos (half_pos hW) (lt_of_not_ge hc)
    linarith
  linarith

lemma ab_sym_unique (W k x₁ x₂ : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ e z, F e z = W * clip01 ((1 + k * z - k * e) / 2) * e) (hW : 0 < W) (hk : 0 < k)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (h₁ : ∀ e, 0 ≤ e → F e x₂ ≤ F x₁ x₂)
    (h₂ : ∀ e, 0 ≤ e → F e x₁ ≤ F x₂ x₁) : k * x₁ = 1 ∧ k * x₂ = 1 := by
  have s1 := ab_share_pos W k x₁ x₂ F hF hW hk hx₂ h₁
  have s2 := ab_share_pos W k x₂ x₁ F hF hW hk hx₁ h₂
  have f1 := ab_br_foc W k x₁ x₂ F hF hW hk hx₁ h₁ s1 (by linarith)
  have f2 := ab_br_foc W k x₂ x₁ F hF hW hk hx₂ h₂ s2 (by linarith)
  constructor <;> linarith

lemma ab_sym_exist (W k x : ℝ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ e z, F e z = W * clip01 ((1 + k * z - k * e) / 2) * e) (hW : 0 < W) (hk : 0 < k)
    (hx : k * x = 1) : (∀ e, 0 ≤ e → F e x ≤ F x x) ∧ k * F x x = W / 2 := by
  have hc : clip01 ((1 + k * x - k * x) / 2) = 1 / 2 := by
    rw [show (1 + k * x - k * x) / 2 = 1 / 2 by ring]; exact ab_clip_eq (by norm_num) (by norm_num)
  have hFx : F x x = W * (1 / 2) * x := by rw [hF, hc]
  refine ⟨?_, ?_⟩
  · intro e he
    rw [hF e x, hFx]
    apply ab_one_le W _ e _ hW.le he
    · intro _
      rw [hx]
      have hxk : x = 1 / k := by field_simp; linarith
      rw [hxk]
      have : W * ((1 + 1 - k * e) / 2) * e * k ≤ W * (1 / 2) * (1 / k) * k := by
        have : W * (1 / 2) * (1 / k) * k = W / 2 := by field_simp
        rw [this]; nlinarith [mul_nonneg hW.le (sq_nonneg (k * e - 1))]
      exact le_of_mul_le_mul_right this hk
    · have : 0 ≤ x := by
        by_contra h; have h := lt_of_not_ge h; nlinarith
      positivity
  · rw [hFx]; linear_combination (W / 2) * hx

end AdBlockers.Allow

open AdBlockers.Allow

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 ∧
      rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      ∀ p₁ p₂ : ℝ, IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p₁ p₂ →
        p₁ = 1 ∧ p₂ = 1 := by
  simp only [BenchPlan.toPlan]
  have hW : 0 < lam + μ := by linarith
  have hF : ∀ e z, rev₁ lam μ β γ .fee .fee e z =
      (lam + μ) * clip01 ((1 + 1 * z - 1 * e) / 2) * e := by
    intro e z; simp only [rev₁, hotellingShare, disNon, disAdb, payAdb, one_mul]; ring
  have hx : (1 : ℝ) * 1 = 1 := by norm_num
  obtain ⟨hbr, hval⟩ := ab_sym_exist (lam + μ) 1 1 (rev₁ lam μ β γ .fee .fee) hF hW one_pos hx
  have hv : rev₁ lam μ β γ .fee .fee 1 1 = (lam + μ) / 2 := by linarith
  refine ⟨⟨zero_le_one, zero_le_one, hbr, ?_⟩, hv, ?_, ?_⟩
  · intro e he; simp only [rev₂]; exact hbr e he
  · simp only [rev₂]; exact hv
  · intro p₁ p₂ h
    obtain ⟨h0, h0', h1, h2⟩ := h
    simp only [rev₂] at h2
    obtain ⟨e1, e2⟩ := ab_sym_unique (lam + μ) 1 p₁ p₂ (rev₁ lam μ β γ .fee .fee) hF hW one_pos
      h0 h0' h1 h2
    constructor <;> linarith
