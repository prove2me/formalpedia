-- Prove2me | solution 1 for AccelSGDGrowth.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:50:19.265083+00:00
-- url     : https://prove2.me/submissions/84f11a72-809e-49bf-be0c-e9b5afa6ae03

import Definitions.Def_AccelSGDGrowth_ClassF

open AccelSGDGrowth in
theorem solution {d : ℕ} {L : ℝ} (hL : 0 < L) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ClassF 0 L f) :
    (∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      f x + inner ℝ (gradient f x) (y - x) + ‖gradient f y - gradient f x‖ ^ 2 / (2 * L) ≤ f y) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ^ 2 / L ≤ inner ℝ (gradient f y - gradient f x) (y - x)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      inner ℝ (gradient f y - gradient f x) (y - x) ≤ L * ‖y - x‖ ^ 2) := by
  have key2 : ∀ x y : EuclideanSpace ℝ (Fin d),
      f x + inner ℝ (gradient f x) (y - x) + ‖gradient f y - gradient f x‖ ^ 2 / (2 * L) ≤ f y := by
    intro x y
    obtain ⟨g, hg⟩ : ∃ g, g = gradient f y - gradient f x := ⟨_, rfl⟩
    rw [← hg]
    have h1 := hf.2.1 y (y - (1 / L) • g)
    have h2 := hf.2.2 x (y - (1 / L) • g)
    have e1 : y - (1 / L) • g - y = -((1 / L) • g) := by abel
    have e2 : y - (1 / L) • g - x = (y - x) - (1 / L) • g := by abel
    rw [e1] at h1
    rw [e2] at h2
    rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul] at h1
    rw [inner_sub_right, real_inner_smul_right] at h2
    have e3 : inner ℝ (gradient f y) g - inner ℝ (gradient f x) g = ‖g‖ ^ 2 := by
      rw [← inner_sub_left, ← hg, real_inner_self_eq_norm_sq]
    have hn : ‖(1 / L)‖ = 1 / L := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn, mul_pow] at h1
    have eA : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = ‖g‖ ^ 2 / (2 * L) := by
      field_simp <;> ring
    have eB : 1 / L * inner ℝ (gradient f y) g - 1 / L * inner ℝ (gradient f x) g
        = 2 * (‖g‖ ^ 2 / (2 * L)) := by
      rw [← mul_sub, e3]; ring
    have e0 : (0:ℝ) / 2 * ‖y - x - (1 / L) • g‖ ^ 2 = 0 := by ring
    linarith
  have key3 : ∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ^ 2 / L ≤ inner ℝ (gradient f y - gradient f x) (y - x) := by
    intro x y
    have h1 := key2 x y
    have h2 := key2 y x
    rw [norm_sub_rev (gradient f x) (gradient f y)] at h2
    have e : x - y = -(y - x) := by abel
    rw [e, inner_neg_right] at h2
    rw [inner_sub_left]
    have e2 : ‖gradient f y - gradient f x‖ ^ 2 / L
        = 2 * (‖gradient f y - gradient f x‖ ^ 2 / (2 * L)) := by ring
    linarith
  have key1 : ∀ x y : EuclideanSpace ℝ (Fin d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖ := by
    intro x y
    have h := key3 x y
    have hcs := real_inner_le_norm (gradient f y - gradient f x) (y - x)
    have h3 : ‖gradient f y - gradient f x‖ ^ 2 ≤ L * (‖gradient f y - gradient f x‖ * ‖y - x‖) :=
      (div_le_iff₀' hL).mp (h.trans hcs)
    rcases (norm_nonneg (gradient f y - gradient f x)).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · apply le_of_mul_le_mul_left _ hpos
      nlinarith
  refine ⟨key1, key2, key3, fun x y => ?_⟩
  have hcs := real_inner_le_norm (gradient f y - gradient f x) (y - x)
  have := mul_le_mul_of_nonneg_right (key1 x y) (norm_nonneg (y - x))
  nlinarith
