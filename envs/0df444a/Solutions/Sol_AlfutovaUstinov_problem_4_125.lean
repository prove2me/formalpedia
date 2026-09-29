-- Prove2me | solution 1 for AlfutovaUstinov.problem_4_125
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T23:45:24.94421+00:00
-- url     : https://prove2.me/submissions/fa6e184a-d39e-463b-a7e8-d67b6dcdd0a7

import Mathlib


theorem solution (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (a x : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hx : x ^ 2 ≡ a [ZMOD p]) : a ^ ((p - 1) / 2) ≡ 1 [ZMOD p] := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have he : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hxp : ¬ (p : ℤ) ∣ x := by
    intro hdx
    apply ha
    have h1 : (p : ℤ) ∣ x ^ 2 := dvd_pow hdx (by norm_num)
    have h2 := dvd_add hx.dvd h1
    rwa [sub_add_cancel] at h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime x p := ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).2 hxp).symm
  have hf := Int.ModEq.pow_card_sub_one_eq_one hp hcop
  calc a ^ ((p - 1) / 2) ≡ (x ^ 2) ^ ((p - 1) / 2) [ZMOD p] := (hx.pow _).symm
    _ = x ^ (p - 1) := by rw [← pow_mul, he]
    _ ≡ 1 [ZMOD p] := hf
