-- Prove2me | solution 1 for AppliedComb.InclExcl.derangements_count
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:28:05.302988+00:00
-- url     : https://prove2.me/submissions/472ee5c2-ee47-41c1-bbca-157dc96c88a2

import Mathlib

lemma ascFac_eq_choose_mul_fac_08caa73f (n k : ℕ) (hk : k ≤ n) :
    Nat.ascFactorial (k + 1) (n - k) = n.choose k * (n - k).factorial := by
  have h1 := Nat.factorial_mul_ascFactorial k (n - k)
  have h2 := Nat.choose_mul_factorial_mul_factorial hk
  rw [Nat.add_sub_cancel' hk] at h1
  have hpos : 0 < k.factorial := Nat.factorial_pos k
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h2]
  ring

theorem solution (n : ℕ) :
    (Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, σ i ≠ i} : ℤ) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ) := by
  have hc : Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, σ i ≠ i} =
      Fintype.card (derangements (Fin n)) := Fintype.card_congr (Equiv.refl _)
  rw [hc, card_derangements_eq_numDerangements, Fintype.card_fin, numDerangements_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [ascFac_eq_choose_mul_fac_08caa73f n k hk']
  push_cast
  ring
