-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_142
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:45.071618+00:00
-- url     : https://prove2.me/submissions/4e94e268-045c-4c27-8041-4c652e1ade8a

import Mathlib


theorem solution :
    (∀ n : ℕ, 0 < n → (Nat.totient n = n - 1 ↔ n.Prime)) ∧
      (∀ n : ℕ, 0 < n → (Nat.totient (2 * n) = 2 * Nat.totient n ↔ Even n)) ∧
      (∀ n k : ℕ, 0 < n → 0 < k → Nat.totient (n ^ k) = n ^ (k - 1) * Nat.totient n) := by
  refine ⟨fun n hn => Nat.totient_eq_iff_prime hn, ?_, ?_⟩
  · intro n hn
    constructor
    · intro h
      by_contra hne
      have hodd : Odd n := Nat.not_even_iff_odd.1 hne
      have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 hodd
      rw [Nat.totient_mul hcop, Nat.totient_two, one_mul] at h
      have hpos : 0 < Nat.totient n := Nat.totient_pos.2 hn
      omega
    · intro h
      exact Nat.totient_mul_of_prime_of_dvd Nat.prime_two (even_iff_two_dvd.1 h)
  · intro n k hn hk
    have h1 := Nat.totient_mul_prod_primeFactors (n ^ k)
    have h2 := Nat.totient_mul_prod_primeFactors n
    rw [Nat.primeFactors_pow n hk.ne'] at h1
    have hP : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have e : n ^ k = n ^ (k - 1) * n := by rw [← pow_succ, Nat.sub_add_cancel hk]
    apply Nat.eq_of_mul_eq_mul_right hP
    calc Nat.totient (n ^ k) * ∏ p ∈ n.primeFactors, p
        = n ^ k * ∏ p ∈ n.primeFactors, (p - 1) := h1
      _ = n ^ (k - 1) * (n * ∏ p ∈ n.primeFactors, (p - 1)) := by rw [e, mul_assoc]
      _ = n ^ (k - 1) * (Nat.totient n * ∏ p ∈ n.primeFactors, p) := by rw [h2]
      _ = n ^ (k - 1) * Nat.totient n * ∏ p ∈ n.primeFactors, p := by ring
