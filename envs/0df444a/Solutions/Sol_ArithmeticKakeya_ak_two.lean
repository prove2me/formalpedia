-- Prove2me | solution 1 for ArithmeticKakeya.ak_two
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:10:47.126921+00:00
-- url     : https://prove2.me/submissions/2e6469b6-5881-4894-9e10-61cbbbc39689

import Mathlib
import Definitions.Def_ArithmeticKakeya_ak

namespace ArithmeticKakeya

theorem ak_two : AK (2 : ℝ) := by
  intro ε hε
  refine ⟨1, one_pos, {(1, 0), (0, 1)}, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num
  · intro G
    set A := G.image (fun g : ℤ × ℤ => (1:ℤ) * g.1 + 0 * g.2)
    set B := G.image (fun g : ℤ × ℤ => (0:ℤ) * g.1 + 1 * g.2)
    have hG : (G.image (fun g : ℤ × ℤ => g.1 - g.2)).card ≤ A.card * B.card := by
      calc (G.image (fun g : ℤ × ℤ => g.1 - g.2)).card ≤ G.card := Finset.card_image_le
        _ ≤ (A ×ˢ B).card := by
          apply Finset.card_le_card
          intro g hg
          simp only [Finset.mem_product, A, B, Finset.mem_image]
          exact ⟨⟨g, hg, by ring⟩, ⟨g, hg, by ring⟩⟩
        _ = A.card * B.card := Finset.card_product _ _
    have key : ∀ M N : ℕ, ((M * N : ℕ) : ℝ) ≤ (max M N : ℝ) ^ ((2:ℝ) + ε) := by
      intro M N
      rcases Nat.eq_zero_or_pos (M * N) with h0 | hpos
      · rw [h0]; simp only [Nat.cast_zero]
        positivity
      · have hM : 1 ≤ (max M N : ℝ) := by
          have : 1 ≤ M := Nat.pos_of_mul_pos_right hpos
          exact le_trans (by exact_mod_cast this) (le_max_left _ _)
        calc ((M * N : ℕ) : ℝ) = (M:ℝ) * N := by push_cast; ring
          _ ≤ (max M N : ℝ) * (max M N : ℝ) :=
              mul_le_mul (le_max_left _ _) (le_max_right _ _) (by positivity) (by positivity)
          _ = (max M N : ℝ) ^ (2:ℝ) := by rw [Real.rpow_two]; ring
          _ ≤ (max M N : ℝ) ^ ((2:ℝ) + ε) := Real.rpow_le_rpow_of_exponent_le hM (by linarith)
    rcases le_total A.card B.card with hAB | hAB
    · refine ⟨(0, 1), by simp, ?_⟩
      have := key A.card B.card
      rw [show (max (A.card : ℝ) (B.card : ℝ)) = B.card from max_eq_right (by exact_mod_cast hAB)] at this
      rw [one_mul]
      exact le_trans (Nat.cast_le.2 hG) this
    · refine ⟨(1, 0), by simp, ?_⟩
      have := key A.card B.card
      rw [show (max (A.card : ℝ) (B.card : ℝ)) = A.card from max_eq_left (by exact_mod_cast hAB)] at this
      rw [one_mul]
      exact le_trans (Nat.cast_le.2 hG) this

end ArithmeticKakeya

theorem solution : ArithmeticKakeya.AK (2 : ℝ) := ArithmeticKakeya.ak_two
