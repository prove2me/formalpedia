-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicCharacterCongruence
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclotomicCharacterCongruence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:03.753636+00:00
-- url     : https://prove2.me/theorems/3522c938-eddf-4e48-b7ec-8ca7b57d14e2
-- title:
--   Peterfalvi (1.10): cyclotomic congruences of character values
-- statement:
--   Formalizes the cyclotomic-integer arithmetic behind Peterfalvi (1.10) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §1, p. 7), including divisibility properties of $1-\varepsilon$ powers for primitive $p$-th roots of unity.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclotomicCharacterCongruence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclotomicCharacterCongruence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RootsOfUnity.Lemmas

namespace OddOrder.RepresentationTheory

open Polynomial Module

/-- For `ε` a primitive `p`-th root of unity (`p` prime) and `0 < k < p`, the cyclotomic factors
`1 - ε^k` and `1 - ε` are **associates**: explicitly `1 - ε = (1 - ε^k)·w` with `w` an algebraic
integer.  Since `gcd(k,p)=1`, `ε^k` is again a primitive `p`-th root, so `ε = (ε^k)^r` for some `r`,
whence `1 - ε = 1 - (ε^k)^r = (1 - ε^k)·∑_{i<r}(ε^k)^i`.  This is the "hard" divisibility direction
(the easy one, `(1-ε) ∣ (1-ε^k)`, is `one_sub_dvd_pow_sub_one`) underlying Peterfalvi (1.10.b). -/
theorem one_sub_pow_dvd_one_sub {p : ℕ} (hp : p.Prime) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ∃ w : ℂ, IsIntegral ℤ w ∧ (1 - ε) = (1 - ε ^ k) * w := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hcop : Nat.Coprime k p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk0 hkp)).symm
  have hεk : IsPrimitiveRoot (ε ^ k) p := hε.pow_of_coprime k hcop
  obtain ⟨r, _, hr⟩ := hεk.eq_pow_of_pow_eq_one hε.pow_eq_one
  have hεk_int : IsIntegral ℤ (ε ^ k) :=
    isIntegral_of_pow_eq_one (n := p) hp.pos.ne'
      (by rw [← pow_mul, mul_comm, pow_mul, hε.pow_eq_one, one_pow])
  have hmem : ε ^ k ∈ integralClosure ℤ ℂ := hεk_int
  refine ⟨∑ i ∈ Finset.range r, (ε ^ k) ^ i, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hmem i)
  · have hgeom : (1 - ε ^ k) * ∑ i ∈ Finset.range r, (ε ^ k) ^ i = 1 - (ε ^ k) ^ r := by
      linear_combination -geom_sum_mul (ε ^ k) r
    rw [hr] at hgeom; exact hgeom.symm

/-- A rational integer `a` with `(a:ℂ) = (b:ℂ)·W` for `b ≠ 0` an integer and `W` an algebraic
integer is divisible by `b` (the rational algebraic integer `W = a/b` is a rational integer). -/
theorem int_dvd_of_intCast_eq_mul_isIntegral {a b : ℤ} (hb : b ≠ 0) {W : ℂ}
    (hW : IsIntegral ℤ W) (h : (a : ℂ) = (b : ℂ) * W) : b ∣ a := by
  have hb' : (b : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hWeq : W = algebraMap ℚ ℂ ((a : ℚ) / (b : ℚ)) := by
    rw [map_div₀, map_intCast, map_intCast, eq_div_iff hb', mul_comm]; exact h.symm
  have hqInt : IsIntegral ℤ ((a : ℚ) / (b : ℚ)) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp (hWeq ▸ hW)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqInt
  refine ⟨m, ?_⟩
  have key : (a : ℚ) = (b : ℚ) * (m : ℚ) := by
    rw [← eq_intCast (algebraMap ℤ ℚ) m, hm]; field_simp
  exact_mod_cast key

/-- **Peterfalvi (1.10.b)** (ℂ-form, global algebraic integers): for `p` prime, `ε` a primitive
`p`-th root of unity, if a rational integer `n` is `(1 - ε)` times an algebraic integer `z`, then
`p ∣ n`.  This is the form actually used in (12.16)/(13.5) — `z` is any algebraic integer of `ℂ`
(matching the Coq/`Z[η]` formulation), no specific cyclotomic field needed.

**Which (1.10.b) to use** (issue 0106): prefer *this* ℂ-form unless you already carry a
`NumberField`/`IsCyclotomicExtension` structure — the abstract form
`int_dvd_of_zeta_sub_one_dvd` says the same thing inside a `p`-th cyclotomic field and pulls
in the number-field machinery with it.

Proof: `∏_{1≤k<p}(1 - ε^k) = p` (`prod_one_sub_pow_eq_order`), and each `(1 - ε^k) ∣ (1 - ε) ∣ n`
(`one_sub_pow_dvd_one_sub`) with integral cofactor, so the product `p` divides `n^{p-1}` with
integral quotient; descending the rational algebraic integer to `ℤ` gives `p ∣ n^{p-1}`, hence
`p ∣ n`. -/
theorem int_dvd_of_one_sub_primRoot_dvd {p : ℕ} (hp : p.Prime) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {n : ℤ} {z : ℂ} (hz : IsIntegral ℤ z)
    (h : (n : ℂ) = (1 - ε) * z) : (p : ℤ) ∣ n := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  -- per-factor cofactors: `(n:ℂ) = (1 - ε^(k+1))·c k`, `c k` an algebraic integer.
  have key : ∀ k : ℕ, ∃ c : ℂ, IsIntegral ℤ c ∧ (k < m → (n : ℂ) = (1 - ε ^ (k + 1)) * c) := by
    intro k
    by_cases hk : k < m
    · obtain ⟨w, hw_int, hw_eq⟩ :=
        one_sub_pow_dvd_one_sub (k := k + 1) hp hε (by omega) (by omega)
      exact ⟨w * z, hw_int.mul hz, fun _ => by rw [h, hw_eq]; ring⟩
    · exact ⟨0, isIntegral_zero, fun hc => absurd hc hk⟩
  choose c hc_int hc_eq using key
  -- `n^m = (∏(1-ε^(k+1)))·(∏ c) = (m+1)·(∏ c)`.
  have hprod_fac : (n : ℂ) ^ m = ((m : ℂ) + 1) * ∏ k ∈ Finset.range m, c k := by
    have e1 : (n : ℂ) ^ m = ∏ _k ∈ Finset.range m, (n : ℂ) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [e1, Finset.prod_congr rfl (fun k hk => hc_eq k (Finset.mem_range.mp hk)),
      Finset.prod_mul_distrib, hε.prod_one_sub_pow_eq_order]
  -- descend `(m+1) ∣ n^m` in `ℤ`.
  have hWint : IsIntegral ℤ (∏ k ∈ Finset.range m, c k) := by
    have : (∏ k ∈ Finset.range m, c k) ∈ integralClosure ℤ ℂ :=
      Subalgebra.prod_mem _ (fun k _ => hc_int k)
    exact this
  have hdvd_pow : ((m : ℤ) + 1) ∣ n ^ m :=
    int_dvd_of_intCast_eq_mul_isIntegral (a := n ^ m) (b := (m : ℤ) + 1)
      (by positivity) hWint (by push_cast; exact hprod_fac)
  have hpZ : Prime ((m : ℤ) + 1) := by
    have := Nat.prime_iff_prime_int.mp hp; push_cast at this; exact this
  exact hpZ.dvd_of_dvd_pow hdvd_pow

/-- **Peterfalvi (1.10.a), per-linear-character core**: for a linear character `α : A → ℂˣ` of a
finite group `A`, a `p`-th-power-trivial element `x` (`x^p = 1`) and any `y`, the difference
`α(xy) - α(y)` is `(1 - ε)` times an algebraic integer (`ε` a primitive `p`-th root of unity).

Proof: `α(xy) - α(y) = (α(x) - 1)·α(y)`; `α(x)^p = 1` so `α(x) = ε^k`; `ε^k - 1 = (1-ε)·(-∑ εⁱ)`;
and `α(y)` is a root of unity, hence integral.  This is the linear-character building block of the
restriction-decomposition proof of (1.10.a) (`⟨x,y⟩` abelian ⟹ constituents are linear). -/
theorem exists_integral_linearChar_apply_sub {p : ℕ} (hp : 0 < p) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {A : Type*} [Group A] [Finite A] (α : A →* ℂˣ)
    {x y : A} (hx : x ^ p = 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ (α (x * y) : ℂ) - (α y : ℂ) = (1 - ε) * z := by
  have : NeZero p := ⟨hp.ne'⟩
  -- `α(x)` is a `p`-th root of unity, hence `= ε^k`
  have hαxp : (α x : ℂ) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  obtain ⟨k, _, hk⟩ := hε.eq_pow_of_pow_eq_one hαxp
  -- `α(y)` is a root of unity (order divides `|A|`), hence integral
  have hαy : IsIntegral ℤ (α y : ℂ) := by
    refine isIntegral_of_pow_eq_one (n := Nat.card A) Nat.card_pos.ne' ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨-(∑ i ∈ Finset.range k, ε ^ i) * (α y : ℂ), ?_, ?_⟩
  · have hε_mem : ε ∈ integralClosure ℤ ℂ := hε.isIntegral hp
    have hsum : IsIntegral ℤ (∑ i ∈ Finset.range k, ε ^ i) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hε_mem i)
    exact hsum.neg.mul hαy
  · have hgeom : ε ^ k - 1 = (1 - ε) * (-(∑ i ∈ Finset.range k, ε ^ i)) := by
      rw [← geom_sum_mul ε k]; ring
    rw [map_mul, Units.val_mul, ← hk]
    linear_combination (α y : ℂ) * hgeom

/-- **Peterfalvi (1.10.a)** (full, virtual-character form): for a finite **abelian** group `A`, a
virtual character `χ ∈ ℤ[Irr A]`, a `p`-th-power-trivial element `x` (`x^p = 1`) and any `y`, the
difference `χ(xy) - χ(y)` is `(1 - ε)` times an algebraic integer (`ε` a primitive `p`-th root).

Proof: the set of class functions with this property is a `ℤ`-submodule (closed under `+`, `ℤ`-smul,
contains `0`); it contains every irreducible character of `A` — each is a linear character
(`exists_linearIrreducibleCharacter_eq_of_isMulCommutative`) so the per-linear-character core
`exists_integral_linearChar_apply_sub` applies — hence it contains `ℤ[Irr A] = span ℤ (Irr A)`. -/
theorem exists_integral_zirr_apply_sub {p : ℕ} (hp : 0 < p) {ε : ℂ} (hε : IsPrimitiveRoot ε p)
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A] {χ : ClassFunction A ℂ}
    (hχ : χ ∈ ZIrr A) {x y : A} (hx : x ^ p = 1) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ χ (x * y) - χ y = (1 - ε) * z := by
  -- the property, as a `ℤ`-submodule of `CF(A)`.
  let M : Submodule ℤ (ClassFunction A ℂ) :=
    { carrier := {ψ | ∃ z : ℂ, IsIntegral ℤ z ∧ ψ (x * y) - ψ y = (1 - ε) * z}
      zero_mem' := ⟨0, isIntegral_zero, by simp⟩
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨z₁, hz₁, e₁⟩ ⟨z₂, hz₂, e₂⟩
        exact ⟨z₁ + z₂, hz₁.add hz₂, by
          simp only [ClassFunction.add_apply]; linear_combination e₁ + e₂⟩
      smul_mem' := by
        rintro c ψ ⟨z, hz, e⟩
        have hcz : IsIntegral ℤ ((c : ℂ) * z) :=
          (isIntegral_algebraMap (R := ℤ) (x := c)).mul hz
        refine ⟨(c : ℂ) * z, hcz, ?_⟩
        have happ : ∀ g, (c • ψ) g = (c : ℂ) * ψ g := fun g => by
          change c • ψ g = (c : ℂ) * ψ g
          rw [zsmul_eq_mul]
        rw [happ, happ]; linear_combination (c : ℂ) * e }
  -- every irreducible character of `A` lies in `M`.
  have hsub : irreducibleCharacters A ⊆ (M : Set (ClassFunction A ℂ)) := by
    intro α hα
    obtain ⟨θ, hθ⟩ :=
      (mem_irreducibleCharacters.mp hα).exists_linearIrreducibleCharacter_eq_of_isMulCommutative
    obtain ⟨z, hz, he⟩ := exists_integral_linearChar_apply_sub hp hε θ hx
    refine ⟨z, hz, ?_⟩
    rw [← hθ]; simpa using he
  -- conclude: `χ ∈ ZIrr A = span ℤ (Irr A) ≤ M`.
  rw [ZIrr_eq_span] at hχ
  exact Submodule.span_le.mpr hsub hχ

/-- **Peterfalvi (1.10.a)** (`G`-form, commuting elements): for a virtual character
`ψ ∈ ℤ[Irr G]` of any finite group `G`, an order-dividing-`p` element `x` (`x^p = 1`) and any `y`
**commuting** with
`x`, `ψ(xy) - ψ(y)` is `(1 - ε)` times an algebraic integer.

Reduce to the abelian subgroup `A = ⟨x, y⟩` (commutative since `x, y` commute): `Res_A ψ ∈ ℤ[Irr A]`
(`restrict_mem_ZIrr`), and `exists_integral_zirr_apply_sub` applies, with `(Res_A ψ)(a) = ψ(a)`. -/
theorem exists_integral_apply_sub_of_commute {p : ℕ} (hp : 0 < p) {ε : ℂ}
    (hε : IsPrimitiveRoot ε p) {G : Type*} [Group G] [Finite G]
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {x y : G} (hx : x ^ p = 1) (hxy : Commute x y) :
    ∃ z : ℂ, IsIntegral ℤ z ∧ ψ (x * y) - ψ y = (1 - ε) * z := by
  set A := Subgroup.closure ({x, y} : Set G) with hA
  have : IsMulCommutative ↥A := by
    refine Subgroup.isMulCommutative_closure (fun a ha b hb => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hxA : x ∈ A := Subgroup.subset_closure (by simp)
  have hyA : y ∈ A := Subgroup.subset_closure (by simp)
  have hres : ClassFunction.restrict A ψ ∈ ZIrr ↥A := ClassFunction.restrict_mem_ZIrr A hψ
  have hx' : (⟨x, hxA⟩ : ↥A) ^ p = 1 := by
    apply Subtype.ext; push_cast; exact hx
  obtain ⟨z, hz, he⟩ := exists_integral_zirr_apply_sub hp hε hres
    (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) hx'
  refine ⟨z, hz, ?_⟩
  rwa [ClassFunction.restrict_apply, ClassFunction.restrict_apply,
    show ((⟨x, hxA⟩ * ⟨y, hyA⟩ : ↥A) : G) = x * y from rfl,
    show ((⟨y, hyA⟩ : ↥A) : G) = y from rfl] at he

end OddOrder.RepresentationTheory


