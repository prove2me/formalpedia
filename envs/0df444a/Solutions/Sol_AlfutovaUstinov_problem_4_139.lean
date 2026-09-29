-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_139
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:54.317761+00:00
-- url     : https://prove2.me/submissions/06e1c30b-b3d2-4425-8dd3-03093b0a1d4d

import Mathlib

namespace AU139Aux

theorem mem_candidates (m : ℕ) (hm : 0 < m) (x : ℕ) (hx : Nat.totient x = m) :
    x ∈ (((Finset.range (m + 2)).filter (fun p => 2 ≤ p ∧ (p - 1) ∣ m)).powerset).image
      (fun S => m * (∏ p ∈ S, p) / ∏ p ∈ S, (p - 1)) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    omega
  rw [Finset.mem_image]
  refine ⟨x.primeFactors, ?_, ?_⟩
  · rw [Finset.mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpx := Nat.dvd_of_mem_primeFactors hp
    have h1 : p - 1 ∣ m := by
      have := Nat.totient_dvd_of_dvd hpx
      rwa [Nat.totient_prime hpp, hx] at this
    have h2 : p - 1 ≤ m := Nat.le_of_dvd hm h1
    have h3 := hpp.two_le
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h3, h1⟩
  · have h1 := Nat.totient_mul_prod_primeFactors x
    rw [hx] at h1
    have hQ : 0 < ∏ p ∈ x.primeFactors, (p - 1) :=
      Finset.prod_pos (fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
    show m * (∏ p ∈ x.primeFactors, p) / ∏ p ∈ x.primeFactors, (p - 1) = x
    rw [h1]
    exact Nat.mul_div_cancel _ hQ

end AU139Aux

theorem solution :
    {x : ℕ | Nat.totient x = 2} = {3, 4, 6} ∧
      {x : ℕ | Nat.totient x = 8} = {15, 16, 20, 24, 30} ∧
      {x : ℕ | Nat.totient x = 12} = {13, 21, 26, 28, 36, 42} ∧
      {x : ℕ | Nat.totient x = 14} = ∅ := by
  have gen : ∀ m : ℕ, 0 < m → ∀ A : Finset ℕ,
      (∀ y ∈ (((Finset.range (m + 2)).filter (fun p => 2 ≤ p ∧ (p - 1) ∣ m)).powerset).image
        (fun S => m * (∏ p ∈ S, p) / ∏ p ∈ S, (p - 1)), Nat.totient y = m → y ∈ A) →
      (∀ y ∈ A, Nat.totient y = m) →
      {x : ℕ | Nat.totient x = m} = (A : Set ℕ) := by
    intro m hm A h1 h2
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact ⟨fun hx => h1 x (AU139Aux.mem_candidates m hm x hx) hx, fun hx => h2 x hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gen 2 (by norm_num) {3, 4, 6} (by decide +kernel) (by decide +kernel)]
    simp
  · rw [gen 8 (by norm_num) {15, 16, 20, 24, 30} (by decide +kernel) (by decide +kernel)]
    simp
  · rw [gen 12 (by norm_num) {13, 21, 26, 28, 36, 42} (by decide +kernel) (by decide +kernel)]
    simp
  · rw [gen 14 (by norm_num) ∅ (by decide +kernel) (by decide +kernel)]
    simp
