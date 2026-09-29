-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:51.543987+00:00
-- url     : https://prove2.me/submissions/d3f1fc87-45d1-4436-99a3-e011f3ece6b5

import Mathlib


theorem solution (p k : ℕ) (hp : p.Prime) (hpk : p = 4 * k + 1) :
    (Nat.factorial (2 * k) : ℤ) ^ 2 + 1 ≡ 0 [ZMOD p] ∧
      (-(Nat.factorial (2 * k) : ℤ)) ^ 2 + 1 ≡ 0 [ZMOD p] := by
  have := Fact.mk hp
  have hfac : ∀ n : ℕ, ((Nat.factorial n : ℕ) : ZMod p) = ∏ i ∈ Finset.range n, ((i : ZMod p) + 1) := by
    intro n
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  have hp0 : ((4 * k + 1 : ℕ) : ZMod p) = 0 := by
    rw [← hpk]; exact ZMod.natCast_self p
  have hterm : ∀ x ∈ Finset.range (2 * k),
      (((2 * k + x : ℕ) : ZMod p) + 1) = -(((2 * k - 1 - x : ℕ) : ZMod p) + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Nat.cast_sub (show x ≤ 2 * k - 1 by omega), Nat.cast_sub (show 1 ≤ 2 * k by omega)]
    push_cast at hp0 ⊢
    linear_combination hp0
  have h4k : ((Nat.factorial (4 * k) : ℕ) : ZMod p) = ((Nat.factorial (2 * k) : ℕ) : ZMod p) ^ 2 := by
    rw [hfac, hfac, show 4 * k = 2 * k + 2 * k by ring, Finset.prod_range_add, sq]
    congr 1
    rw [Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.card_range,
      Even.neg_one_pow ⟨k, by ring⟩, one_mul]
    exact Finset.prod_range_reflect (fun x => ((x : ZMod p) + 1)) (2 * k)
  have hW : ((Nat.factorial (p - 1) : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hmain : ((Nat.factorial (2 * k) : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have e : p - 1 = 4 * k := by omega
    rw [e, h4k] at hW
    rw [hW]; ring
  have hz : (Nat.factorial (2 * k) : ℤ) ^ 2 + 1 ≡ 0 [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hmain
  refine ⟨hz, ?_⟩
  rw [neg_sq]; exact hz
