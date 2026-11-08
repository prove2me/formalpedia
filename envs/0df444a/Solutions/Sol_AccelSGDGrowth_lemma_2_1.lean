-- Prove2me | solution 1 for AccelSGDGrowth.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:22:58.176638+00:00
-- url     : https://prove2.me/submissions/54794cb6-cc1e-4f56-964b-175af73d7515

import Definitions.Def_AccelSGDGrowth_ClassFInf

open AccelSGDGrowth in
theorem solution {d : ℕ} {m : ℝ} (hm : 0 < m) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ClassFInf m f) :
    (∀ x y : EuclideanSpace ℝ (Fin d),
      f y ≤ f x + inner ℝ (gradient f x) (y - x) +
        ‖gradient f y - gradient f x‖ ^ 2 / (2 * m)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      m * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient f y - gradient f x) (y - x)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin d),
      m * ‖y - x‖ ≤ ‖gradient f y - gradient f x‖) := by
  obtain ⟨-, hineq⟩ := hf
  have hswap : ∀ x y : EuclideanSpace ℝ (Fin d),
      inner ℝ (gradient f y) (x - y) = -inner ℝ (gradient f y) (y - x) := by
    intro x y
    rw [← inner_neg_right, neg_sub]
  have part2 : ∀ x y : EuclideanSpace ℝ (Fin d),
      m * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient f y - gradient f x) (y - x) := by
    intro x y
    have h1 := hineq x y
    have h2 := hineq y x
    rw [hswap, norm_sub_rev] at h2
    rw [inner_sub_left]
    linarith
  refine ⟨fun x y => ?_, part2, fun x y => ?_⟩
  · have h2 := hineq y x
    rw [hswap, norm_sub_rev] at h2
    have hcs := real_inner_le_norm (gradient f y - gradient f x) (y - x)
    have hsplit : inner ℝ (gradient f y) (y - x) =
        inner ℝ (gradient f x) (y - x) + inner ℝ (gradient f y - gradient f x) (y - x) := by
      rw [inner_sub_left]; ring
    obtain ⟨A, hA⟩ : ∃ A, A = ‖gradient f y - gradient f x‖ ^ 2 / (2 * m) := ⟨_, rfl⟩
    have hA2 : A * (2 * m) = ‖gradient f y - gradient f x‖ ^ 2 := by
      rw [hA]; field_simp
    have hamgm : ‖gradient f y - gradient f x‖ * ‖y - x‖ ≤ A + m / 2 * ‖y - x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖gradient f y - gradient f x‖ - m * ‖y - x‖)]
    rw [← hA]
    linarith
  · have h := part2 x y
    have hcs := real_inner_le_norm (gradient f y - gradient f x) (y - x)
    rcases (norm_nonneg (y - x)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · have : ‖y - x‖ * (m * ‖y - x‖) ≤ ‖y - x‖ * ‖gradient f y - gradient f x‖ := by nlinarith
      exact le_of_mul_le_mul_left this h0
