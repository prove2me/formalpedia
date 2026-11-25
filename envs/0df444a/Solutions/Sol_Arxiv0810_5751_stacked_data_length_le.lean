-- Prove2me | solution 1 for Arxiv0810_5751.stacked_data_length_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:56:48.079142+00:00
-- url     : https://prove2.me/submissions/343592c7-492e-4814-9905-1ebae2fa7ee3

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

set_option autoImplicit false

open MeasureTheory Matrix
open scoped ComplexOrder
namespace Arxiv0810_5751

lemma sd_card (N : ℕ) : (crossBaselines N).card = N * (N - 1) / 2 := by
  unfold crossBaselines
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have e : ∀ a : Fin N, (∑ b : Fin N, if a < b then 1 else 0) = N - 1 - a.1 := by
    intro a
    rw [← Finset.card_filter, ← Fin.card_Ioi]
    congr 1
    ext b; simp
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

theorem stacked_data_length_le (N : ℕ) :
    (∀ B : Finset (Fin N × Fin N), B ⊆ crossBaselines N →
      Fintype.card (VisIndex B) ≤ 2 * N * (N - 1)) ∧
    Fintype.card (VisIndex (crossBaselines N)) = 2 * N * (N - 1) := by
  have hev : (N * (N - 1)) % 2 = 0 := Nat.even_iff.1 (Nat.even_mul_pred_self N)
  have key : 4 * (N * (N - 1) / 2) = 2 * N * (N - 1) := by
    have : 2 * N * (N - 1) = 2 * (N * (N - 1)) := by ring
    rw [this]; omega
  have hc : ∀ B : Finset (Fin N × Fin N), Fintype.card (VisIndex B) = B.card * 4 := by
    intro B; simp [VisIndex, Fintype.card_prod]
  refine ⟨fun B hB => ?_, ?_⟩
  · rw [hc, ← key, mul_comm 4]
    exact Nat.mul_le_mul_right 4 ((Finset.card_le_card hB).trans (sd_card N).le)
  · rw [hc, sd_card, ← key, mul_comm]

end Arxiv0810_5751

open Arxiv0810_5751 in
theorem solution (N : ℕ) :
    (∀ B : Finset (Fin N × Fin N), B ⊆ crossBaselines N →
      Fintype.card (VisIndex B) ≤ 2 * N * (N - 1)) ∧
    Fintype.card (VisIndex (crossBaselines N)) = 2 * N * (N - 1) :=
  Arxiv0810_5751.stacked_data_length_le N
