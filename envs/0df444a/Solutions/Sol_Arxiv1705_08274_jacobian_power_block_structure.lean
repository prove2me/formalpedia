-- Prove2me | solution 1 for Arxiv1705_08274.jacobian_power_block_structure
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:49:20.943121+00:00
-- url     : https://prove2.me/submissions/6dae3ab5-4cdb-4b1f-af69-63ea22850bdd

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

open Arxiv1705_08274 in
theorem solution {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (m : ℕ) (hm : 1 ≤ m) :
    S.jacobian ^ 2 = fromBlocks (S.alpha * S.alpha - S.beta * S.beta)
      (-(S.alpha * S.beta) + S.beta * S.alpha) (S.beta * S.alpha - S.alpha * S.beta)
      (-(S.beta * S.beta) + S.alpha * S.alpha) ∧
    (∃ γ₁₁ γ₁₂ : Matrix (Dir N) (Dir N) ℝ,
      S.jacobian ^ (2 * m) = fromBlocks γ₁₁ γ₁₂ γ₁₂ γ₁₁) ∧
    (∃ η₁₁ η₁₂ : Matrix (Dir N) (Dir N) ℝ,
      S.jacobian ^ (2 * m - 1) = fromBlocks η₁₁ (-η₁₂) η₁₂ (-η₁₁)) := by
  have hJ2 : S.jacobian ^ 2 = fromBlocks (S.alpha * S.alpha - S.beta * S.beta)
      (-(S.alpha * S.beta) + S.beta * S.alpha) (S.beta * S.alpha - S.alpha * S.beta)
      (-(S.beta * S.beta) + S.alpha * S.alpha) := by
    rw [sq, DOModel.jacobian, fromBlocks_multiply]
    congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg] <;> abel
  have heven : ∀ j : ℕ, ∃ A B : Matrix (Dir N) (Dir N) ℝ, S.jacobian ^ (2 * j) = fromBlocks A B B A := by
    intro j
    induction j with
    | zero => exact ⟨1, 0, by simp [fromBlocks_one]⟩
    | succ j ih =>
      obtain ⟨A, B, h⟩ := ih
      refine ⟨A * (S.alpha * S.alpha - S.beta * S.beta) + B * (S.beta * S.alpha - S.alpha * S.beta),
        A * (-(S.alpha * S.beta) + S.beta * S.alpha) + B * (-(S.beta * S.beta) + S.alpha * S.alpha), ?_⟩
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, h, hJ2, fromBlocks_multiply]
      congr 1
      · rw [show S.beta * S.alpha - S.alpha * S.beta = -(S.alpha * S.beta) + S.beta * S.alpha by abel,
          show -(S.beta * S.beta) + S.alpha * S.alpha = S.alpha * S.alpha - S.beta * S.beta by abel]
        abel
      · rw [show S.beta * S.alpha - S.alpha * S.beta = -(S.alpha * S.beta) + S.beta * S.alpha by abel,
          show -(S.beta * S.beta) + S.alpha * S.alpha = S.alpha * S.alpha - S.beta * S.beta by abel]
        abel
  refine ⟨hJ2, heven m, ?_⟩
  obtain ⟨A, B, h⟩ := heven (m - 1)
  refine ⟨A * S.alpha + B * S.beta, B * S.alpha + A * S.beta, ?_⟩
  rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ, h, DOModel.jacobian, fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_neg] <;> abel
