-- Prove2me | solution 2 for AdBlockers.Allow.case_2_fee_fee
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:58.325204+00:00
-- url     : https://prove2.me/submissions/643c1c79-197d-4b71-b119-6ebcea0fb8ef

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

set_option autoImplicit false
open AdBlockers.Allow

lemma dz_clip_mid {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : clip01 z = z := by
  simp [clip01, min_eq_right h1, max_eq_right h0]

lemma dz_clip_hi {z : ℝ} (h : 1 ≤ z) : clip01 z = 1 := by
  simp [clip01, min_eq_left h]

lemma dz_clip_lo {z : ℝ} (h : z ≤ 0) : clip01 z = 0 := by
  unfold clip01
  exact max_eq_left (le_trans (min_le_right _ _) h)

lemma dz_clip_pos {z : ℝ} (h : 0 < z) : 0 < clip01 z :=
  lt_max_of_lt_right (lt_min one_pos h)

lemma dz_clip_le_one (z : ℝ) : clip01 z ≤ 1 := by
  unfold clip01
  exact max_le zero_le_one (min_le_left _ _)

lemma dz_clip_nonneg (z : ℝ) : 0 ≤ clip01 z := le_max_left _ _

lemma dz_ne_unique (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : ∀ e : ℝ, 0 ≤ e → e * clip01 ((1 + b - e) / 2) ≤ a * clip01 ((1 + b - a) / 2))
    (h2 : ∀ e : ℝ, 0 ≤ e → e * clip01 ((1 + a - e) / 2) ≤ b * clip01 ((1 + a - b) / 2)) :
    a = 1 ∧ b = 1 := by
  -- Step 1: |a - b| < 1
  have hba : b - a < 1 := by
    by_contra hcon
    push_neg at hcon
    have hy : clip01 ((1 + a - b) / 2) = 0 := dz_clip_lo (by linarith)
    have e2 := h2 1 zero_le_one
    rw [hy, mul_zero, one_mul] at e2
    have ha0 : a = 0 := by
      by_contra hne
      have : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
      have := dz_clip_pos (z := (1 + a - 1) / 2) (by linarith)
      linarith
    subst ha0
    have e1 := h1 1 zero_le_one
    rw [zero_mul, one_mul] at e1
    have := dz_clip_pos (z := (1 + b - 1) / 2) (by linarith)
    linarith
  have hab : a - b < 1 := by
    by_contra hcon
    push_neg at hcon
    have hy : clip01 ((1 + b - a) / 2) = 0 := dz_clip_lo (by linarith)
    have e2 := h1 1 zero_le_one
    rw [hy, mul_zero, one_mul] at e2
    have hb0 : b = 0 := by
      by_contra hne
      have : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
      have := dz_clip_pos (z := (1 + b - 1) / 2) (by linarith)
      linarith
    subst hb0
    have e1 := h2 1 zero_le_one
    rw [zero_mul, one_mul] at e1
    have := dz_clip_pos (z := (1 + a - 1) / 2) (by linarith)
    linarith
  have hx : clip01 ((1 + b - a) / 2) = (1 + b - a) / 2 := dz_clip_mid (by linarith) (by linarith)
  have hy : clip01 ((1 + a - b) / 2) = (1 + a - b) / 2 := dz_clip_mid (by linarith) (by linarith)
  rw [hx] at h1
  rw [hy] at h2
  -- Step 2: bounds a, b ≤ 3
  have hb3 : b ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have e := h1 (b - 1) (by linarith)
    have : (1 + b - (b - 1)) / 2 = 1 := by ring
    rw [this, dz_clip_hi le_rfl] at e
    nlinarith [mul_pos (show 0 < a - (b - 1) by linarith) (show 0 < a - 2 by linarith)]
  have ha3 : a ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have e := h2 (a - 1) (by linarith)
    have : (1 + a - (a - 1)) / 2 = 1 := by ring
    rw [this, dz_clip_hi le_rfl] at e
    nlinarith [mul_pos (show 0 < b - (a - 1) by linarith) (show 0 < b - 2 by linarith)]
  -- Step 3: first order conditions
  have ea : a = (1 + b) / 2 := by
    have e := h1 ((1 + b) / 2) (by linarith)
    have : (1 + b - (1 + b) / 2) / 2 = (1 + b) / 4 := by ring
    rw [this, dz_clip_mid (by linarith) (by linarith)] at e
    nlinarith [sq_nonneg (1 + b - 2 * a)]
  have eb : b = (1 + a) / 2 := by
    have e := h2 ((1 + a) / 2) (by linarith)
    have : (1 + a - (1 + a) / 2) / 2 = (1 + a) / 4 := by ring
    rw [this, dz_clip_mid (by linarith) (by linarith)] at e
    nlinarith [sq_nonneg (1 + a - 2 * b)]
  constructor <;> linarith

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 ∧
      rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      ∀ p₁ p₂ : ℝ, IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p₁ p₂ →
        p₁ = 1 ∧ p₂ = 1 := by
  have hr1 : ∀ d1 d2 : ℝ, rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan d1 d2
      = (lam + μ) * (d1 * clip01 ((1 + d2 - d1) / 2)) := by
    intro d1 d2
    simp [rev₁, disNon, disAdb, payAdb, BenchPlan.toPlan, hotellingShare]
    ring
  have hr2 : ∀ d1 d2 : ℝ, rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan d1 d2
      = (lam + μ) * (d2 * clip01 ((1 + d1 - d2) / 2)) := by
    intro d1 d2
    simp [rev₂, rev₁, disNon, disAdb, payAdb, BenchPlan.toPlan, hotellingShare]
    ring
  have hK : 0 < lam + μ := add_pos hlam hμ
  have hval1 : (1:ℝ) * clip01 ((1 + 1 - 1) / 2) = 1 / 2 := by
    rw [show ((1:ℝ) + 1 - 1) / 2 = 1 / 2 by norm_num, dz_clip_mid (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨zero_le_one, zero_le_one, ?_, ?_⟩
    · intro e he
      rw [hr1, hr1]
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      rw [hval1]
      by_cases h2 : e ≤ 2
      · rw [dz_clip_mid (by linarith) (by linarith)]
        nlinarith [sq_nonneg (e - 1)]
      · push_neg at h2
        rw [dz_clip_lo (by linarith), mul_zero]; norm_num
    · intro e he
      rw [hr2, hr2]
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      rw [hval1]
      by_cases h2 : e ≤ 2
      · rw [dz_clip_mid (by linarith) (by linarith)]
        nlinarith [sq_nonneg (e - 1)]
      · push_neg at h2
        rw [dz_clip_lo (by linarith), mul_zero]; norm_num
  · rw [hr1, hval1]; ring
  · rw [hr2, hval1]; ring
  · intro p₁ p₂ h
    obtain ⟨hp1, hp2, h1, h2⟩ := h
    refine dz_ne_unique p₁ p₂ hp1 hp2 ?_ ?_
    · intro e he
      have := h1 e he
      rw [hr1, hr1] at this
      exact le_of_mul_le_mul_left this hK
    · intro e he
      have := h2 e he
      rw [hr2, hr2] at this
      exact le_of_mul_le_mul_left this hK
