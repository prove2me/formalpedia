-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_122
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:18.281984+00:00
-- url     : https://prove2.me/submissions/67c14c29-9013-4554-893f-cf5a6ece49a2

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (q : ℕ) (hq : q.Prime)
    (hqd : q ∣ 2 ^ p - 1) : ∃ k : ℕ, q = 2 * k * p + 1 := by
  have := Fact.mk hq
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2p : 2 ∣ 2 ^ p := dvd_pow_self 2 (by omega)
    omega
  have hpow : (2 : ZMod q) ^ p = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ p - 1) q).2 hqd
    rw [Nat.cast_sub h1] at h
    push_cast at h
    exact sub_eq_zero.1 h
  have h20 : (2 : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hpow
    exact zero_ne_one hpow
  have hord : orderOf (2 : ZMod q) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      have h10 : (1 : ZMod q) = 0 := by linear_combination h
      exact one_ne_zero h10
    · exact h
  have hdvd1 : p ∣ q - 1 := by
    rw [← hord]; exact ZMod.orderOf_dvd_card_sub_one h20
  obtain ⟨m, hm⟩ := hq.odd_of_ne_two hq2
  have h2dvd : 2 ∣ q - 1 := ⟨m, by omega⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2dvd hdvd1
  refine ⟨k, ?_⟩
  have := hq.two_le
  have e : q = 2 * p * k + 1 := by omega
  rw [e]; ring
