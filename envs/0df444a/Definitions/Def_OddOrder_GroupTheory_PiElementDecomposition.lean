-- Prove2me | Definitions.Def_OddOrder_GroupTheory_PiElementDecomposition
-- name    : OddOrder_GroupTheory_PiElementDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:31.135816+00:00
-- url     : https://prove2.me/theorems/40825709-e7c2-4429-915d-7e7fb2375fff
-- title:
--   $\pi$-part / $\pi'$-part decomposition of a group element
-- statement:
--   For a finite-order element $g$ and a set of primes $\pi$, $g$ factors uniquely as $g=ab$ with $a$ a $\pi$-element, $b$ a $\pi'$-element, and $a,b$ commuting powers of $g$. This is the two-part Hall decomposition of $\langle g\rangle$, the elementary foundation of the $\sigma$-decompositions of Bender–Glauberman.
--
--   Main declarations: `IsPiElement` (`g` is a `π`-element: every prime dividing `orderOf g` lies in `π`); `natPiPart` (The `π`-part of a natural number: `∏ p^(vₚ n)` over the primes `p ∈ π` dividing `n`).
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/PiElementDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/PiElementDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group

namespace OddOrder.GroupTheory

/-- `g` is a `π`-element: every prime dividing `orderOf g` lies in `π`. -/
def IsPiElement (π : Set ℕ) {G : Type*} [Monoid G] (g : G) : Prop :=
  ∀ p ∈ (orderOf g).primeFactors, p ∈ π

/-- The identity is a `π`-element for any `π` (its order is `1`, no prime factors). -/
theorem isPiElement_one (π : Set ℕ) {G : Type*} [Monoid G] : IsPiElement π (1 : G) := by
  intro p hp; simp at hp

open Classical in
/-- The `π`-part of a natural number: `∏ p^(vₚ n)` over the primes `p ∈ π` dividing `n`. -/
noncomputable def natPiPart (π : Set ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, if p ∈ π then p ^ n.factorization p else 1

theorem natPiPart_ne_zero (π : Set ℕ) (n : ℕ) : natPiPart π n ≠ 0 := by
  classical
  rw [natPiPart]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  split_ifs with hpπ
  · exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).pos.ne'
  · exact one_ne_zero

/-- `∏ p^(vₚ n)` over all prime factors of `n` is `n`. -/
theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- The `π`-part times the `π′`-part recovers `n`. -/
theorem natPiPart_mul_compl (π : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    natPiPart π n * natPiPart πᶜ n = n := by
  classical
  rw [natPiPart, natPiPart, ← Finset.prod_mul_distrib]
  conv_rhs => rw [← prod_primeFactors_pow_factorization hn]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hpπ : p ∈ π <;> simp [hpπ, Set.mem_compl_iff]

/-- Every prime dividing the `π`-part of `n` lies in `π`. -/
theorem mem_of_mem_primeFactors_natPiPart {π : Set ℕ} {n : ℕ} {p : ℕ}
    (hp : p ∈ (natPiPart π n).primeFactors) : p ∈ π := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ natPiPart π n := Nat.dvd_of_mem_primeFactors hp
  rw [natPiPart] at hpdvd
  obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hpp.prime hpdvd
  by_cases hqπ : q ∈ π
  · rw [if_pos hqπ] at hpq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpq)
    rw [heq]; exact hqπ
  · rw [if_neg hqπ] at hpq
    exact absurd (Nat.dvd_one.mp hpq) hpp.ne_one

/-- The `π`-part and the `π′`-part of `n` are coprime. -/
theorem coprime_natPiPart_compl (π : Set ℕ) (n : ℕ) :
    Nat.Coprime (natPiPart π n) (natPiPart πᶜ n) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hp1 : p ∈ (natPiPart π n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_left _ _), natPiPart_ne_zero π n⟩
  have hp2 : p ∈ (natPiPart πᶜ n).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), natPiPart_ne_zero πᶜ n⟩
  exact (mem_of_mem_primeFactors_natPiPart hp2) (mem_of_mem_primeFactors_natPiPart hp1)

variable {G : Type*} [Group G]

/-- **Existence of the `π`-decomposition** of a finite-order element.  For `g` of finite order
and a set of primes `π`, `g = a * b` with `a` a `π`-element, `b` a `π′`-element, both commuting
powers of `g`.  (BG §1: the σ-decomposition for the two-block partition `{π, π′}`.) -/
theorem exists_isPiElement_mul [Finite G] (π : Set ℕ) (g : G) :
    ∃ a b : G, a * b = g ∧ Commute a b ∧ IsPiElement π a ∧ IsPiElement πᶜ b ∧
      a ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g := by
  set n := orderOf g with hn_def
  have hn : n ≠ 0 := (orderOf_pos g).ne'
  set nπ := natPiPart π n with hnπ
  set nπ' := natPiPart πᶜ n with hnπ'
  have hco : Nat.Coprime nπ nπ' := coprime_natPiPart_compl π n
  have hmul : nπ * nπ' = n := natPiPart_mul_compl π hn
  -- Exponents via CRT: `e ≡ 1 (mod nπ)`, `e ≡ 0 (mod nπ')`; `f ≡ 0`, `f ≡ 1`.
  have he : (Nat.chineseRemainder hco 1 0 : ℕ) ≡ 1 [MOD nπ] ∧
      (Nat.chineseRemainder hco 1 0 : ℕ) ≡ 0 [MOD nπ'] := (Nat.chineseRemainder hco 1 0).2
  have hf : (Nat.chineseRemainder hco 0 1 : ℕ) ≡ 0 [MOD nπ] ∧
      (Nat.chineseRemainder hco 0 1 : ℕ) ≡ 1 [MOD nπ'] := (Nat.chineseRemainder hco 0 1).2
  set e := (Nat.chineseRemainder hco 1 0 : ℕ) with he_def
  set f := (Nat.chineseRemainder hco 0 1 : ℕ) with hf_def
  refine ⟨g ^ e, g ^ f, ?_, (Commute.refl g).pow_pow e f, ?_, ?_,
    pow_mem (Subgroup.mem_zpowers g) e, pow_mem (Subgroup.mem_zpowers g) f⟩
  · -- `g^e * g^f = g`: `e + f ≡ 1 (mod n)`.
    rw [← pow_add]
    have hsum_nπ : e + f ≡ 1 [MOD nπ] := by simpa using Nat.ModEq.add he.1 hf.1
    have hsum_nπ' : e + f ≡ 1 [MOD nπ'] := by simpa using Nat.ModEq.add he.2 hf.2
    have hsum : e + f ≡ 1 [MOD n] := by
      rw [← hmul]; exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hsum_nπ, hsum_nπ'⟩
    have hgef : g ^ (e + f) = g ^ 1 := pow_eq_pow_iff_modEq.mpr (hn_def ▸ hsum)
    rw [hgef, pow_one]
  · -- `g^e` is a `π`-element: `(g^e)^nπ = 1`, so `orderOf (g^e) ∣ nπ`.
    intro p hp
    obtain ⟨t, ht⟩ := (Nat.modEq_zero_iff_dvd).mp he.2
    have hpow : (g ^ e) ^ nπ = 1 := by
      rw [← pow_mul]
      have hexp : e * nπ = n * t := by rw [ht, ← hmul]; ring
      rw [hexp, pow_mul, hn_def, pow_orderOf_eq_one, one_pow]
    exact mem_of_mem_primeFactors_natPiPart
      (Nat.primeFactors_mono (orderOf_dvd_of_pow_eq_one hpow) (natPiPart_ne_zero π n) hp)
  · -- `g^f` is a `π′`-element: `(g^f)^nπ' = 1`, so `orderOf (g^f) ∣ nπ'`.
    intro p hp
    obtain ⟨t, ht⟩ := (Nat.modEq_zero_iff_dvd).mp hf.1
    have hpow : (g ^ f) ^ nπ' = 1 := by
      rw [← pow_mul]
      have hexp : f * nπ' = n * t := by rw [ht, ← hmul]; ring
      rw [hexp, pow_mul, hn_def, pow_orderOf_eq_one, one_pow]
    exact mem_of_mem_primeFactors_natPiPart
      (Nat.primeFactors_mono (orderOf_dvd_of_pow_eq_one hpow) (natPiPart_ne_zero πᶜ n) hp)

/-- A `π`-element's inverse is a `π`-element (same order). -/
theorem isPiElement_inv {π : Set ℕ} {a : G} (ha : IsPiElement π a) : IsPiElement π a⁻¹ := by
  intro p hp; rw [orderOf_inv] at hp; exact ha p hp

/-- The orders of a `π`-element and a `π′`-element are coprime. -/
theorem coprime_orderOf_of_isPiElement [Finite G] {π : Set ℕ} {a b : G}
    (ha : IsPiElement π a) (hb : IsPiElement πᶜ b) : Nat.Coprime (orderOf a) (orderOf b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h
  have hpb : p ∈ (orderOf b).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_right _ _), (orderOf_pos b).ne'⟩
  have hpa : p ∈ (orderOf a).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Nat.gcd_dvd_left _ _), (orderOf_pos a).ne'⟩
  exact (hb p hpb) (ha p hpa)

/-- The product of two commuting `π`-elements is a `π`-element. -/
theorem isPiElement_mul_of_commute [Finite G] {π : Set ℕ} {a b : G} (hcomm : Commute a b)
    (ha : IsPiElement π a) (hb : IsPiElement π b) : IsPiElement π (a * b) := by
  intro p hp
  have hpow : (a * b) ^ (orderOf a * orderOf b) = 1 := by
    rw [hcomm.mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, one_mul,
      mul_comm (orderOf a) (orderOf b), pow_mul, pow_orderOf_eq_one, one_pow]
  have hne : orderOf a * orderOf b ≠ 0 :=
    Nat.mul_ne_zero (orderOf_pos a).ne' (orderOf_pos b).ne'
  have hpin := Nat.primeFactors_mono (orderOf_dvd_of_pow_eq_one hpow) hne hp
  rw [Nat.primeFactors_mul (orderOf_pos a).ne' (orderOf_pos b).ne', Finset.mem_union] at hpin
  exact hpin.elim (ha p) (hb p)

/-- Two elements of `⟨g⟩` commute. -/
theorem commute_of_mem_zpowers {g a b : G} (ha : a ∈ Subgroup.zpowers g)
    (hb : b ∈ Subgroup.zpowers g) : Commute a b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact (Commute.refl g).zpow_zpow i j

/-- If `g = a * b` with `a`, `b` commuting of coprime order, then `a` is a power of `g`. -/
theorem mem_zpowers_of_mul_eq [Finite G] {g a b : G} (hab : a * b = g) (hcomm : Commute a b)
    (hco : Nat.Coprime (orderOf a) (orderOf b)) : a ∈ Subgroup.zpowers g := by
  have hgb : g ^ orderOf b = a ^ orderOf b := by
    rw [← hab, hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco.symm
  exact Subgroup.mem_zpowers_iff.mpr
    ⟨((orderOf b * m : ℕ) : ℤ), by rw [zpow_natCast, pow_mul, hgb, hm]⟩

/-- **Uniqueness of the `π`-decomposition**: the `π`-part and `π′`-part of `g` are determined.
Two factorizations `g = a*b = a'*b'` into a commuting `π`-element and `π′`-element agree. -/
theorem isPiElement_mul_unique [Finite G] {π : Set ℕ} {g a b a' b' : G}
    (hab : a * b = g) (hcomm : Commute a b) (ha : IsPiElement π a) (hb : IsPiElement πᶜ b)
    (hab' : a' * b' = g) (hcomm' : Commute a' b') (ha' : IsPiElement π a')
    (hb' : IsPiElement πᶜ b') : a = a' ∧ b = b' := by
  -- All four factors lie in the cyclic group `⟨g⟩`.
  have haz : a ∈ Subgroup.zpowers g :=
    mem_zpowers_of_mul_eq hab hcomm (coprime_orderOf_of_isPiElement ha hb)
  have ha'z : a' ∈ Subgroup.zpowers g :=
    mem_zpowers_of_mul_eq hab' hcomm' (coprime_orderOf_of_isPiElement ha' hb')
  have hbz : b ∈ Subgroup.zpowers g := by
    have hbeq : b = a⁻¹ * g := by rw [← hab]; group
    rw [hbeq]; exact mul_mem (inv_mem haz) (Subgroup.mem_zpowers g)
  have hb'z : b' ∈ Subgroup.zpowers g := by
    have hb'eq : b' = a'⁻¹ * g := by rw [← hab']; group
    rw [hb'eq]; exact mul_mem (inv_mem ha'z) (Subgroup.mem_zpowers g)
  -- `u := a'⁻¹ * a = b' * b⁻¹` is both a `π`-element and a `π′`-element, hence trivial.
  have hu_eq : a'⁻¹ * a = b' * b⁻¹ := by
    have h : a * b = a' * b' := hab.trans hab'.symm
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hu_pi : IsPiElement π (a'⁻¹ * a) :=
    isPiElement_mul_of_commute ((commute_of_mem_zpowers ha'z haz).inv_left)
      (isPiElement_inv ha') ha
  have hu_compl : IsPiElement πᶜ (a'⁻¹ * a) := by
    rw [hu_eq]
    exact isPiElement_mul_of_commute ((commute_of_mem_zpowers hb'z hbz).inv_right)
      hb' (isPiElement_inv hb)
  have hu1 : a'⁻¹ * a = 1 := by
    rw [← orderOf_eq_one_iff]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpin : p ∈ (orderOf (a'⁻¹ * a)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos _).ne'⟩
    exact (hu_compl p hpin) (hu_pi p hpin)
  have haa' : a = a' := (inv_mul_eq_one.mp hu1).symm
  refine ⟨haa', ?_⟩
  have heq : a * b = a * b' := by rw [hab, haa']; exact hab'.symm
  exact mul_left_cancel heq

end OddOrder.GroupTheory


