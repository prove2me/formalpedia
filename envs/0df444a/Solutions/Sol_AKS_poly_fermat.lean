-- Prove2me | solution 1 for AKS.poly_fermat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:09:37.962115+00:00
-- url     : https://prove2.me/submissions/63c382f5-554b-4c38-a75c-a7fb60bc827e

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

open Polynomial in
theorem g71a_not_dvd_choose (n p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hlt : p < n) :
    ¬ n ∣ n.choose p := by
  intro h
  obtain ⟨t, ht⟩ := h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have key := Nat.add_one_mul_choose_eq n' p'
  rw [ht] at key
  have hpos : 0 < n' + 1 := by omega
  have h2 : n'.choose p' = t * (p' + 1) := by
    have : (n' + 1) * n'.choose p' = (n' + 1) * (t * (p' + 1)) := by rw [key]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have := Fact.mk hp
  have luc := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n' p' (p' + 1) _
  have hmod : n' % (p' + 1) = p' := by
    have h1 : n' + 1 ≡ 0 [MOD p' + 1] := (Nat.modEq_zero_iff_dvd).2 hpn
    have h0 : p' + 1 ≡ 0 [MOD p' + 1] := (Nat.modEq_zero_iff_dvd).2 dvd_rfl
    have h3 : n' ≡ p' [MOD p' + 1] := Nat.ModEq.add_right_cancel' 1 (h1.trans h0.symm)
    rw [h3]; exact Nat.mod_eq_of_lt (by omega)
  rw [hmod, Nat.mod_eq_of_lt (by omega : p' < p' + 1), Nat.div_eq_of_lt (by omega : p' < p' + 1),
    Nat.choose_self, Nat.choose_zero_right, h2] at luc
  have : (t * (p' + 1)) % (p' + 1) = 1 % (p' + 1) := luc
  rw [Nat.mul_mod_left] at this
  have hp2 := hp.two_le
  rw [Nat.mod_eq_of_lt (by omega : 1 < p' + 1)] at this
  omega

open Polynomial in
theorem solution (n a : ℕ) (hn : 2 ≤ n) (ha : Nat.gcd a n = 1) :
    Nat.Prime n ↔ polyFermat n a := by
  unfold polyFermat
  constructor
  · intro hp
    have := Fact.mk hp
    rw [add_pow_char, ← C_pow, ZMod.pow_card]
  · intro h
    by_contra hnp
    set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hle : p ≤ n := Nat.minFac_le (by omega)
    have hlt : p < n := by
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exact absurd (h' ▸ hp) hnp
    have hc := congrArg (fun q => Polynomial.coeff q p) h
    simp only [coeff_X_add_C_pow, coeff_add, coeff_X_pow, coeff_C] at hc
    have hne : p ≠ n := by omega
    have hne0 : p ≠ 0 := hp.ne_zero
    simp only [hne, hne0, if_false, add_zero] at hc
    have hu : IsUnit ((a : ZMod n)) := (ZMod.unitOfCoprime a ha).isUnit
    have hc' : ((n.choose p : ℕ) : ZMod n) = 0 := ((hu.pow (n - p)).mul_right_eq_zero).1 hc
    exact g71a_not_dvd_choose n p hp hpn hlt ((ZMod.natCast_eq_zero_iff _ _).1 hc')
