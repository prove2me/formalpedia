-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_114
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:02.673991+00:00
-- url     : https://prove2.me/submissions/a5ff057d-5e73-4440-bb94-e67d362eb5d7

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) (k : ℕ)
    (hk : IsLeast {j : ℕ | 0 < j ∧ a ^ j ≡ 1 [ZMOD p]} k) : k ∣ p - 1 := by
  obtain ⟨⟨hk0, hak⟩, hmin⟩ := hk
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime a p := ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).2 ha).symm
  have hf : a ^ (p - 1) ≡ 1 [ZMOD p] := Int.ModEq.pow_card_sub_one_eq_one hp hcop
  have hr : a ^ ((p - 1) % k) ≡ 1 [ZMOD p] := by
    have h1 : a ^ (p - 1) = (a ^ k) ^ ((p - 1) / k) * a ^ ((p - 1) % k) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h2 : (a ^ k) ^ ((p - 1) / k) * a ^ ((p - 1) % k) ≡
        1 ^ ((p - 1) / k) * a ^ ((p - 1) % k) [ZMOD p] :=
      (hak.pow _).mul_right _
    rw [one_pow, one_mul, ← h1] at h2
    exact h2.symm.trans hf
  by_contra hndvd
  have hpos : 0 < (p - 1) % k := by
    rcases Nat.eq_zero_or_pos ((p - 1) % k) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hndvd
    · exact h
  have hmem : (p - 1) % k ∈ {j : ℕ | 0 < j ∧ a ^ j ≡ 1 [ZMOD p]} := by
    simp only [Set.mem_ofPred_eq]
    exact ⟨hpos, hr⟩
  have h1 := hmin hmem
  have h2 := Nat.mod_lt (p - 1) hk0
  omega
