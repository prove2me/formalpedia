-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_111
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:44:56.951951+00:00
-- url     : https://prove2.me/submissions/d92d0e3e-b6ae-45e6-a16d-ab4f99d44380

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ k : ℕ, 0 < k ∧ p ∣ ∑ i ∈ Finset.range k, 10 ^ i := by
  by_cases h3 : p = 3
  · subst h3
    exact ⟨3, by norm_num, by decide⟩
  · refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    have hcop : Nat.Coprime 10 p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have h' : p ∣ 2 * 5 := by norm_num; exact h
      rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h'')
      · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h'')
    have hf := Nat.ModEq.pow_card_sub_one_eq_one hp hcop
    have hg : (∑ i ∈ Finset.range (p - 1), 10 ^ i) * 9 + 1 = 10 ^ (p - 1) := by
      have h := geom_sum_mul_add 9 (p - 1)
      rw [show (9 : ℕ) + 1 = 10 by norm_num] at h
      exact h
    rw [← hg] at hf
    have h9 : (∑ i ∈ Finset.range (p - 1), 10 ^ i) * 9 ≡ 0 [MOD p] := by
      have h' : (∑ i ∈ Finset.range (p - 1), 10 ^ i) * 9 + 1 ≡ 0 + 1 [MOD p] := by
        rw [zero_add]; exact hf
      exact Nat.ModEq.add_right_cancel' 1 h'
    have hdvd : p ∣ (∑ i ∈ Finset.range (p - 1), 10 ^ i) * 9 := Nat.modEq_zero_iff_dvd.1 h9
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact h
    · exfalso
      have h' : p ∣ 3 * 3 := by norm_num; exact h
      rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h'' <;>
        exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'')
