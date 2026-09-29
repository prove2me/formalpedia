-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_141
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:57.114358+00:00
-- url     : https://prove2.me/submissions/48761fa8-90ab-43c5-a297-8a53adc1c407

import Mathlib

namespace AU141Aux

theorem keyPQ (x : ℕ) (hx : 0 < x) (c : ℕ) (h : c * Nat.totient x = x) :
    ∏ p ∈ x.primeFactors, p = c * ∏ p ∈ x.primeFactors, (p - 1) := by
  have h1 := Nat.totient_mul_prod_primeFactors x
  apply Nat.eq_of_mul_eq_mul_left hx
  calc x * ∏ p ∈ x.primeFactors, p = c * Nat.totient x * ∏ p ∈ x.primeFactors, p := by rw [h]
    _ = c * (Nat.totient x * ∏ p ∈ x.primeFactors, p) := by ring
    _ = c * (x * ∏ p ∈ x.primeFactors, (p - 1)) := by rw [h1]
    _ = x * (c * ∏ p ∈ x.primeFactors, (p - 1)) := by ring

theorem mem_of_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℕ) (hq : q.Prime)
    (h : q ∣ ∏ p ∈ S, p) : q ∈ S := by
  obtain ⟨a, ha, hqa⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h
  rw [(Nat.prime_dvd_prime_iff_eq hq (hS a ha)).1 hqa]
  exact ha

theorem eq_empty (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (h : ∏ p ∈ S, p = ∏ p ∈ S, (p - 1)) : S = ∅ := by
  by_contra hne
  have hlt : ∏ p ∈ S, (p - 1) < ∏ p ∈ S, p :=
    Finset.prod_lt_prod_of_nonempty (fun p hp => by have := (hS p hp).two_le; omega)
      (fun p hp => by have := (hS p hp).two_le; omega) (Finset.nonempty_iff_ne_empty.2 hne)
  omega

theorem split (S : Finset ℕ) (q : ℕ) (hq : q ∈ S) (f : ℕ → ℕ) :
    ∏ p ∈ S, f p = f q * ∏ p ∈ S.erase q, f p :=
  (Finset.mul_prod_erase S f hq).symm

theorem case2 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (h : ∏ p ∈ S, p = 2 * ∏ p ∈ S, (p - 1)) : S = {2} := by
  have h2 : 2 ∈ S := mem_of_dvd S hS 2 Nat.prime_two ⟨_, h⟩
  have hS' : ∀ p ∈ S.erase 2, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
  rw [split S 2 h2 (fun p => p), split S 2 h2 (fun p => p - 1)] at h
  have h' : ∏ p ∈ S.erase 2, p = ∏ p ∈ S.erase 2, (p - 1) := by
    simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
    omega
  have he := eq_empty _ hS' h'
  rw [← Finset.insert_erase h2, he]
  decide

theorem case3 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (h : ∏ p ∈ S, p = 3 * ∏ p ∈ S, (p - 1)) : S = {2, 3} := by
  have h3 : 3 ∈ S := mem_of_dvd S hS 3 Nat.prime_three ⟨_, h⟩
  have hS' : ∀ p ∈ S.erase 3, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
  rw [split S 3 h3 (fun p => p), split S 3 h3 (fun p => p - 1)] at h
  have h' : ∏ p ∈ S.erase 3, p = 2 * ∏ p ∈ S.erase 3, (p - 1) := by
    simp only [show (3 : ℕ) - 1 = 2 from rfl] at h
    omega
  have he := case2 _ hS' h'
  rw [← Finset.insert_erase h3, he]
  decide

theorem case4 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (h : ∏ p ∈ S, p = 4 * ∏ p ∈ S, (p - 1)) : False := by
  have h2 : 2 ∈ S := mem_of_dvd S hS 2 Nat.prime_two ⟨2 * ∏ p ∈ S, (p - 1), by rw [h]; ring⟩
  have hS' : ∀ p ∈ S.erase 2, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
  rw [split S 2 h2 (fun p => p), split S 2 h2 (fun p => p - 1)] at h
  have h' : ∏ p ∈ S.erase 2, p = 2 * ∏ p ∈ S.erase 2, (p - 1) := by
    simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
    omega
  exact Finset.notMem_erase 2 S (mem_of_dvd _ hS' 2 Nat.prime_two ⟨_, h'⟩)

end AU141Aux

theorem solution :
    {x : ℕ | 0 < x ∧ 2 * Nat.totient x = x} = {x | ∃ α : ℕ, 0 < α ∧ x = 2 ^ α} ∧
      {x : ℕ | 0 < x ∧ 3 * Nat.totient x = x} =
        {x | ∃ α β : ℕ, 0 < α ∧ 0 < β ∧ x = 2 ^ α * 3 ^ β} ∧
      {x : ℕ | 0 < x ∧ 4 * Nat.totient x = x} = ∅ := by
  have hpf : ∀ x : ℕ, ∀ p ∈ x.primeFactors, p.Prime :=
    fun x p hp => Nat.prime_of_mem_primeFactors hp
  have hprod : ∀ x : ℕ, x ≠ 0 → ∏ p ∈ x.primeFactors, p ^ x.factorization p = x := by
    intro x hx
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hx]
    rw [Finsupp.prod, Nat.support_factorization]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h⟩
      have hS := AU141Aux.case2 _ (hpf x) (AU141Aux.keyPQ x hx 2 h)
      have h2 : 2 ∈ x.primeFactors := by rw [hS]; simp
      refine ⟨x.factorization 2, Nat.Prime.factorization_pos_of_dvd Nat.prime_two hx.ne'
        (Nat.dvd_of_mem_primeFactors h2), ?_⟩
      have := hprod x hx.ne'
      rw [hS, Finset.prod_singleton] at this
      exact this.symm
    · rintro ⟨α, hα, rfl⟩
      refine ⟨by positivity, ?_⟩
      rw [Nat.totient_prime_pow Nat.prime_two hα]
      obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
      rw [Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 from rfl]
      ring
  · ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, h⟩
      have hS := AU141Aux.case3 _ (hpf x) (AU141Aux.keyPQ x hx 3 h)
      have h2 : 2 ∈ x.primeFactors := by rw [hS]; simp
      have h3 : 3 ∈ x.primeFactors := by rw [hS]; simp
      refine ⟨x.factorization 2, x.factorization 3,
        Nat.Prime.factorization_pos_of_dvd Nat.prime_two hx.ne' (Nat.dvd_of_mem_primeFactors h2),
        Nat.Prime.factorization_pos_of_dvd Nat.prime_three hx.ne' (Nat.dvd_of_mem_primeFactors h3),
        ?_⟩
      have := hprod x hx.ne'
      rw [hS, Finset.prod_insert (by decide), Finset.prod_singleton] at this
      exact this.symm
    · rintro ⟨α, β, hα, hβ, rfl⟩
      refine ⟨by positivity, ?_⟩
      rw [Nat.totient_mul (Nat.Coprime.pow α β (by norm_num)),
        Nat.totient_prime_pow Nat.prime_two hα, Nat.totient_prime_pow Nat.prime_three hβ]
      obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 from rfl,
        show (3 : ℕ) - 1 = 2 from rfl]
      ring
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx h
    exact AU141Aux.case4 _ (hpf x) (AU141Aux.keyPQ x hx 4 h)
