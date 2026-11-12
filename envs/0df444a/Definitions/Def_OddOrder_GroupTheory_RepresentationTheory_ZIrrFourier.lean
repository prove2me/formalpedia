-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier
-- name    : OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:09.843634+00:00
-- url     : https://prove2.me/theorems/19efc81a-7ba7-4aea-bf0c-5f3f401b0708
-- title:
--   Fourier coefficients of virtual characters
-- statement:
--   For a finite group $G$ with $|G|$ invertible in $\mathbb{C}$, irreducible characters are orthonormal. A virtual character $\varphi\in\mathbb{Z}[\mathrm{Irr}\,G]$ is a finite integer combination of irreducibles, so its Fourier coefficient $\langle\varphi,\chi\rangle$ at an irreducible $\chi$ is an integer. This file develops that API as the prerequisite for the finite combinatorial core of Peterfalvi §3 (1.4) (`isometry_difference_pair_structure`).
--
--   Declarations include `irreducibleCharacter_inner_eq_ite` (orthonormality in inner-product form), `inner_sum_left` (left-linearity of the inner product over finite sums), `irr_cf_inner`, `mem_ZIrr_repr` (a virtual character is a finite combination of irreducibles), `inner_eq_coeff_of_repr` (the coefficient is recovered by the inner product) and `inner_smul_right`.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ZIrrFourier.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ZIrrFourier.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RowOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsReal
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- Orthonormality of irreducible characters in inner-product form:
`⟨χ, ψ⟩ = δ_{χ,ψ}`.  This is `characterTableRowOrthogonality` restated through the
`ClassFunction.inner` pairing. -/
theorem irreducibleCharacter_inner_eq_ite (χ ψ : IrreducibleCharacter G) :
    ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) =
      if χ = ψ then 1 else 0 := by
  by_cases h : χ = ψ
  · subst h
    rw [if_pos rfl, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.1 χ
  · rw [if_neg h, ← characterTableRowPairing_eq_inner]
    exact characterTableRowOrthogonality.2 h

/-- The Fourier coefficient `⟨φ, χ⟩` of a virtual character `φ ∈ ZIrr G` at an irreducible
character `χ` is an integer. -/
theorem mem_ZIrr_inner_int (χ : IrreducibleCharacter G) {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ (χ : ClassFunction G ℂ) = (m : ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      have heq := irreducibleCharacter_inner_eq_ite (⟨x, hx⟩ : IrreducibleCharacter G) χ
      rw [show ((⟨x, hx⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = x from rfl] at heq
      by_cases h : (⟨x, hx⟩ : IrreducibleCharacter G) = χ
      · refine ⟨1, ?_⟩; rw [heq, if_pos h]; norm_num
      · refine ⟨0, ?_⟩; rw [heq, if_neg h]; norm_num
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_left, hmx, hmy]
      push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, hm]
      push_cast; ring

omit [Finite G] in
/-- Left-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → ClassFunction G ℂ)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (∑ i ∈ s, f i) ψ =
      ∑ i ∈ s, ClassFunction.inner (f i) ψ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_left, ih]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- Orthonormality at the level of irreducible class functions (not the subtype index):
for `a, b` in `irreducibleCharacters G`, `⟨a, b⟩ = δ_{a,b}`. -/
theorem irr_cf_inner {a b : ClassFunction G ℂ}
    (ha : a ∈ irreducibleCharacters G) (hb : b ∈ irreducibleCharacters G) :
    ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
  have key := irreducibleCharacter_inner_eq_ite
    (⟨a, ha⟩ : IrreducibleCharacter G) (⟨b, hb⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at key
  rw [key]
  by_cases h : a = b
  · rw [if_pos h, if_pos (Subtype.ext h)]
  · rw [if_neg h, if_neg fun he => h (Subtype.ext_iff.mp he)]

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- A virtual character `φ ∈ ZIrr G` is a finite `ℂ`-linear combination of irreducible
characters with integer coefficients (recorded as a `Finsupp` supported on `Irr(G)`). -/
theorem mem_ZIrr_repr {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a := by
  rw [ZIrr_eq_span] at hφ
  obtain ⟨c, hsupp, hsum⟩ := Submodule.mem_span_set.mp hφ
  refine ⟨c, hsupp, ?_⟩
  rw [← hsum, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) a).symm

open scoped Classical in
/-- The Fourier coefficient of an integer span representation is recovered by the inner
product: `⟨∑ c_a • a, χ⟩ = c_χ`. -/
theorem inner_eq_coeff_of_repr (χ : IrreducibleCharacter G)
    {c : ClassFunction G ℂ →₀ ℤ} (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) (χ : ClassFunction G ℂ) =
      (c (χ : ClassFunction G ℂ) : ℂ) := by
  rw [inner_sum_left]
  have hχ : (χ : ClassFunction G ℂ) ∈ irreducibleCharacters G := χ.mem_irreducibleCharacters
  have step : (∑ a ∈ c.support, ClassFunction.inner ((c a : ℂ) • a) (χ : ClassFunction G ℂ))
      = ∑ a ∈ c.support, (if a = (χ : ClassFunction G ℂ) then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, irr_cf_inner (hsupp (Finset.mem_coe.mpr ha)) hχ,
      mul_ite, mul_one, mul_zero]
  rw [step, Finset.sum_ite_eq' c.support (χ : ClassFunction G ℂ) (fun a => (c a : ℂ))]
  by_cases hmem : (χ : ClassFunction G ℂ) ∈ c.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, Finsupp.notMem_support_iff.mp hmem, Int.cast_zero]

omit [Finite G] in
/-- Conjugate-linearity of `ClassFunction.inner` over a scalar in the right argument. -/
theorem inner_smul_right (c : ℂ) (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ (c • ψ) = star c * ClassFunction.inner φ ψ := by
  have h : ClassFunction.innerSum φ (c • ψ) = star c * ClassFunction.innerSum φ ψ := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ClassFunction.smul_apply, star_mul']
    ring
  rw [ClassFunction.inner, ClassFunction.inner, h]; ring

omit [Finite G] in
/-- **Conjugate symmetry of `ClassFunction.inner`:** `⟨ψ, φ⟩ = conj ⟨φ, ψ⟩`.
The unscaled sum `∑ φ(g) conj(ψ(g))` is conjugate-symmetric, and the normalizing factor
`⅟|G|` is real. -/
theorem inner_conj_symm (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner ψ φ = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum ψ φ = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hcard : star (⅟(Nat.card G : ℂ)) = ⅟(Nat.card G : ℂ) := by
    rw [show (⅟(Nat.card G : ℂ)) = ((Nat.card G : ℂ))⁻¹ from invOf_eq_inv _,
      star_inv₀, Complex.star_def, Complex.conj_natCast]
  rw [ClassFunction.inner, ClassFunction.inner, hsum, star_mul', hcard]

omit [Finite G] in
/-- **Conjugation invariance of `ClassFunction.inner`:** `⟨φ̄, ψ̄⟩ = conj ⟨φ, ψ⟩`.
Conjugating both arguments conjugates the unscaled sum termwise, and the normalizing
factor `⅟|G|` is real. -/
theorem inner_conj_conj (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ.conj ψ.conj = star (ClassFunction.inner φ ψ) := by
  have hsum : ClassFunction.innerSum φ.conj ψ.conj = star (ClassFunction.innerSum φ ψ) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, star_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [ClassFunction.conj_apply, star_mul', star_star]
  have hcard : star (⅟(Nat.card G : ℂ)) = ⅟(Nat.card G : ℂ) := by
    rw [show (⅟(Nat.card G : ℂ)) = ((Nat.card G : ℂ))⁻¹ from invOf_eq_inv _,
      star_inv₀, Complex.star_def, Complex.conj_natCast]
  rw [ClassFunction.inner, ClassFunction.inner, hsum, star_mul', hcard]

omit [Finite G] in
/-- `⟨φ, φ⟩ = (|G| : ℂ)⁻¹ · ∑_g ‖φ(g)‖²` as the real cast of a nonnegative real.
The unscaled sum `∑_g φ(g) · conj(φ(g)) = ∑_g ‖φ(g)‖²` and the factor `⅟|G|` is the
positive real `(|G| : ℝ)⁻¹`. -/
theorem inner_self_eq_realCast (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ =
      ((((Nat.card G : ℝ)⁻¹) * ∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
  have hsum : ClassFunction.innerSum φ φ =
      ((∑ g : G, Complex.normSq (φ g) : ℝ) : ℂ) := by
    rw [ClassFunction.innerSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  rw [ClassFunction.inner, hsum,
    show (⅟(Nat.card G : ℂ)) = ((Nat.card G : ℂ))⁻¹ from invOf_eq_inv _]
  push_cast
  ring

omit [Finite G] in
/-- **Positive semidefiniteness:** `0 ≤ (⟨φ, φ⟩).re`. -/
theorem inner_self_re_nonneg (φ : ClassFunction G ℂ) :
    0 ≤ (ClassFunction.inner φ φ).re := by
  rw [inner_self_eq_realCast, Complex.ofReal_re]
  have hcard : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hsum : (0 : ℝ) ≤ ∑ g : G, Complex.normSq (φ g) :=
    Finset.sum_nonneg fun g _ => Complex.normSq_nonneg (φ g)
  positivity

omit [Finite G] in
/-- **Positive definiteness:** if `(⟨φ, φ⟩).re = 0` then `φ = 0`.  Over `ℂ`,
`(⟨φ, φ⟩).re = (|G| : ℝ)⁻¹ · ∑_g ‖φ(g)‖²`; the positive factor forces every
`‖φ(g)‖² = 0`, hence `φ(g) = 0` for all `g`. -/
theorem eq_zero_of_inner_self_re_eq_zero {φ : ClassFunction G ℂ}
    (h : (ClassFunction.inner φ φ).re = 0) : φ = 0 := by
  rw [inner_self_eq_realCast, Complex.ofReal_re] at h
  have hcard : (Nat.card G : ℝ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < Nat.card G := by
      exact_mod_cast Nat.card_pos
    positivity
  have hsum : ∑ g : G, Complex.normSq (φ g) = 0 :=
    (mul_eq_zero.mp h).resolve_left hcard
  have hterm : ∀ g ∈ (Finset.univ : Finset G), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun g _ => Complex.normSq_nonneg (φ g)).mp hsum
  ext g
  rw [ClassFunction.zero_apply]
  exact Complex.normSq_eq_zero.mp (hterm g (Finset.mem_univ g))

omit [Finite G] in
/-- Right-linearity of `ClassFunction.inner` over a finite sum. -/
theorem inner_sum_right {ι : Type*} (φ : ClassFunction G ℂ) (s : Finset ι)
    (f : ι → ClassFunction G ℂ) :
    ClassFunction.inner φ (∑ i ∈ s, f i) =
      ∑ i ∈ s, ClassFunction.inner φ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_right, ih]

/-- **Parseval (norm form)** for an integer span representation: the squared norm is the
sum of squared integer coefficients. -/
theorem inner_self_eq_sum_sq_of_repr {c : ClassFunction G ℂ →₀ ℤ}
    (hsupp : ↑c.support ⊆ irreducibleCharacters G) :
    ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a)
        (∑ a ∈ c.support, (c a : ℂ) • a) =
      ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [inner_smul_right]
  have hb' : b ∈ irreducibleCharacters G := hsupp (Finset.mem_coe.mpr hb)
  have hcoeff : ClassFunction.inner (∑ a ∈ c.support, (c a : ℂ) • a) b = (c b : ℂ) := by
    have h := inner_eq_coeff_of_repr (⟨b, hb'⟩ : IrreducibleCharacter G) hsupp
    rwa [show ((⟨b, hb'⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) = b from rfl] at h
  rw [hcoeff, star_intCast]; ring

/-- A virtual character `φ ∈ ZIrr G` has integer Fourier coefficients and its squared norm
is the sum of their squares. -/
theorem mem_ZIrr_inner_self_eq_sum_sq {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    ∃ c : ClassFunction G ℂ →₀ ℤ, (↑c.support ⊆ irreducibleCharacters G) ∧
      φ = ∑ a ∈ c.support, (c a : ℂ) • a ∧
      ClassFunction.inner φ φ = ∑ a ∈ c.support, (c a : ℂ) ^ 2 := by
  obtain ⟨c, hsupp, hrepr⟩ := mem_ZIrr_repr hφ
  refine ⟨c, hsupp, hrepr, ?_⟩
  rw [hrepr]
  exact inner_self_eq_sum_sq_of_repr hsupp

/-- Finite integer-vector combinatorics: if integer coefficients on a finite set `s`
are all nonzero and their squares sum to `2`, then `s` has exactly two elements, each
with coefficient `±1`. -/
theorem exists_pair_of_sum_sq_eq_two {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 2) :
    ∃ α β : ι, α ≠ β ∧ s = {α, β} ∧
      (c α = 1 ∨ c α = -1) ∧ (c β = 1 ∨ c β = -1) := by
  classical
  have hsq2 : ∀ n : ℤ, n ^ 2 ≠ 2 := by
    intro n hn
    have h1 : (n - 1) * (n + 1) = 1 := by linear_combination hn
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hge : ∀ a ∈ s, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard2 : s.card ≤ 2 := by
    have hle : (s.card : ℤ) ≤ ∑ a ∈ s, c a ^ 2 := by
      calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ s, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsum] at hle
    omega
  have hcard : s.card = 2 := by
    rcases Nat.lt_or_ge s.card 2 with hlt | hge2
    · interval_cases hc : s.card
      · rw [Finset.card_eq_zero] at hc; subst hc; simp at hsum
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        rw [Finset.sum_singleton] at hsum
        exact absurd hsum (hsq2 (c a))
    · omega
  obtain ⟨α, β, hαβ, rfl⟩ := Finset.card_eq_two.mp hcard
  rw [Finset.sum_pair hαβ] at hsum
  have h1 := hge α (by simp)
  have h2 := hge β (by simp)
  have hα1 : c α ^ 2 = 1 := by omega
  have hβ1 : c β ^ 2 = 1 := by omega
  refine ⟨α, β, hαβ, rfl, ?_, ?_⟩
  · rw [pow_two] at hα1; exact mul_self_eq_one_iff.mp hα1
  · rw [pow_two] at hβ1; exact mul_self_eq_one_iff.mp hβ1

/-- **`dirr_small_norm` (Peterfalvi §3, mathcomp `dirr_small_norm`), norm-`2` case.**  A virtual
character `φ ∈ ZIrr G` with `‖φ‖² = 2` is a **signed sum of two distinct irreducible characters**:
`φ = ε_α·α + ε_β·β` with `α, β ∈ Irr G`, `α ≠ β`, and signs `ε_α, ε_β ∈ {±1}`.

Assembled from the layer-2 Fourier API: `mem_ZIrr_inner_self_eq_sum_sq` writes `‖φ‖²` as the sum of
squared integer Fourier coefficients over `c.support ⊆ Irr G`, and `exists_pair_of_sum_sq_eq_two`
forces exactly two nonzero coefficients, each `±1`.  This is the constituent-count input to the §3
rigidity lemma `eq_signed_sub_cTIiso` (issue 9076). -/
theorem exists_signed_pair_of_mem_ZIrr_inner_self_eq_two {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 2) :
    ∃ (α β : ClassFunction G ℂ) (εα εβ : ℤ),
      IsIrreducibleCharacter α ∧ IsIrreducibleCharacter β ∧ α ≠ β ∧
      (εα = 1 ∨ εα = -1) ∧ (εβ = 1 ∨ εβ = -1) ∧
      φ = (εα : ℂ) • α + (εβ : ℂ) • β := by
  classical
  obtain ⟨c, hsupp, hrepr, hnorm_sum⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  rw [hnorm] at hnorm_sum
  -- `‖φ‖² = ∑_{a ∈ supp} (c a)²` in `ℂ`, and `= 2`, so the integer sum of squares is `2`.
  have hsum_int : ∑ a ∈ c.support, (c a) ^ 2 = 2 := by
    have hc : ((∑ a ∈ c.support, (c a) ^ 2 : ℤ) : ℂ) = 2 := by
      push_cast; exact hnorm_sum.symm
    exact_mod_cast hc
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α, β, hαβ, hsupport_eq, hα1, hβ1⟩ := exists_pair_of_sum_sq_eq_two hne hsum_int
  rw [hsupport_eq, Finset.sum_pair hαβ] at hrepr
  have hα_mem : α ∈ (↑c.support : Set (ClassFunction G ℂ)) := by rw [hsupport_eq]; simp
  have hβ_mem : β ∈ (↑c.support : Set (ClassFunction G ℂ)) := by rw [hsupport_eq]; simp
  exact ⟨α, β, c α, c β, mem_irreducibleCharacters.mp (hsupp hα_mem),
    mem_irreducibleCharacters.mp (hsupp hβ_mem), hαβ, hα1, hβ1, hrepr⟩

/-- For an integer `c`, `c ≤ c²` (since `c (c - 1) ≥ 0`). -/
theorem int_le_sq (c : ℤ) : c ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1), sq_nonneg c]

/-- Equality `c = c²` holds for an integer iff `c ∈ {0, 1}`. -/
theorem int_eq_sq_iff (c : ℤ) : c = c ^ 2 ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have : c * (c - 1) = 0 := by ring_nf; linarith [h]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> norm_num

/-- **Finite integer Cauchy–Schwarz.** `∑_{a ∈ s} c a ≤ ∑_{a ∈ s} (c a)²`. -/
theorem finset_sum_le_sum_sq {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    ∑ a ∈ s, c a ≤ ∑ a ∈ s, (c a) ^ 2 :=
  Finset.sum_le_sum fun a _ => int_le_sq (c a)

/-- **Tightness of integer Cauchy–Schwarz.** The sum and the sum of squares are
equal iff every coefficient is `0` or `1`. -/
theorem finset_sum_eq_sum_sq_iff {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    (∑ a ∈ s, c a = ∑ a ∈ s, (c a) ^ 2) ↔ ∀ a ∈ s, c a = 0 ∨ c a = 1 := by
  constructor
  · intro h a ha
    exact (int_eq_sq_iff (c a)).mp
      ((Finset.sum_eq_sum_iff_of_le fun a _ => int_le_sq (c a)).mp h a ha)
  · intro h
    exact Finset.sum_congr rfl fun a ha => (int_eq_sq_iff (c a)).mpr (h a ha)

open scoped Classical in
omit [Finite G] in
/-- **Coefficient recovery in an orthonormal family.** If `⟨a, b⟩ = δ_{a,b}` for all
`a, b ∈ s`, then the Fourier coefficient of `X = ∑_{a ∈ s} (c a) • a` at `b ∈ s` is `c b`. -/
theorem inner_orthonormalSum_eq_coeff {s : Finset (ClassFunction G ℂ)} {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    {b : ClassFunction G ℂ} (hb : b ∈ s) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) b = (c b : ℂ) := by
  classical
  rw [inner_sum_left]
  have step : (∑ a ∈ s, ClassFunction.inner ((c a : ℂ) • a) b)
      = ∑ a ∈ s, (if a = b then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, horth a ha b hb, mul_ite, mul_one, mul_zero]
  rw [step, Finset.sum_ite_eq' s b (fun a => (c a : ℂ)), if_pos hb]

open scoped Classical in
omit [Finite G] in
/-- **Parseval (norm form) for an orthonormal family.** With `⟨a, b⟩ = δ_{a,b}` on `s`, the
squared norm of `X = ∑_{a ∈ s} (c a) • a` is `∑_{a ∈ s} (c a)²`. -/
theorem inner_self_orthonormalSum_eq_sum_sq {s : Finset (ClassFunction G ℂ)}
    {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) (∑ a ∈ s, (c a : ℂ) • a) =
      ∑ a ∈ s, (c a : ℂ) ^ 2 := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [inner_smul_right, inner_orthonormalSum_eq_coeff horth hb, star_intCast]
  ring

open scoped Classical in
omit [Finite G] in
/-- **Inner product against the all-ones sum.** With `⟨a, b⟩ = δ_{a,b}` on `s`, the inner
product of `X = ∑_{a ∈ s} (c a) • a` against the unsigned sum `∑_{a ∈ s} a` is `∑_{a ∈ s} c a`.
This is the middle identity of Peterfalvi (5.4.a): `‖χ‖² = ⟨X, ∑_{α} α⟩ = ∑_{α} ⟨X, α⟩`. -/
theorem inner_orthonormalSum_sum_eq_sum_coeff {s : Finset (ClassFunction G ℂ)}
    {c : ClassFunction G ℂ → ℤ}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) (∑ a ∈ s, a) =
      ∑ a ∈ s, (c a : ℂ) := by
  rw [inner_sum_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  exact inner_orthonormalSum_eq_coeff horth hb

open scoped Classical in
omit [Finite G] in
/-- **Squared norm of an unsigned sum over an orthonormal family.** With `⟨a, b⟩ = δ_{a,b}`
on `s`, the squared norm of `∑_{a ∈ s} a` is the cardinality `|s|`.  This is the
`coeff ≡ 1` case of Parseval, used in Peterfalvi (5.6.3) to read
`‖χ̄^{τ₂}‖² = |R(χ) - E|` off the signed sum. -/
theorem inner_self_sum_orthonormal_eq_card {s : Finset (ClassFunction G ℂ)}
    (horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0) :
    ClassFunction.inner (∑ a ∈ s, a) (∑ a ∈ s, a) = (s.card : ℂ) := by
  classical
  rw [inner_sum_left, Finset.sum_congr rfl (fun a ha => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [inner_sum_right, Finset.sum_eq_single a]
    · rw [horth a ha a ha, if_pos rfl]
    · intro b hb hba; rw [horth a ha b hb, if_neg (Ne.symm hba)]
    · intro hna; exact absurd ha hna

open scoped Classical in
omit [Finite G] in
/-- **Pythagoras for an orthogonal family plus an orthogonal residual.**
Let `v : ι → ClassFunction G ℂ` (indexed over `s : Finset ι`) be **orthogonal** with real
gram `⟨v i, v j⟩ = if i = j then (m i : ℂ) else 0`, and let `Z` be orthogonal to every
`v i` (`i ∈ s`).  Then the squared norm of `w = (∑ i ∈ s, (c i : ℂ) • v i) + Z` is the
real number `∑ i ∈ s, (c i)² · m i + (⟨Z, Z⟩).re`.

This is the Hilbert-space identity behind Peterfalvi (5.6.2): writing the orthogonal part
`Y = ∑ i, c i · χ_i^{τ₁} + Z` against the orthogonal family `χ_i^{τ₁}` (norms `‖χ_i‖²`),
`‖Y‖²` splits as a sum of squares plus `‖Z‖²`. -/
theorem inner_self_orthogonalSum_add_re {ι : Type*} (s : Finset ι)
    (v : ι → ClassFunction G ℂ) (c : ι → ℝ) (m : ι → ℝ) (Z : ClassFunction G ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, ClassFunction.inner (v i) (v j) =
      if i = j then (m i : ℂ) else 0)
    (hZ : ∀ i ∈ s, ClassFunction.inner Z (v i) = 0) :
    (ClassFunction.inner ((∑ i ∈ s, (c i : ℂ) • v i) + Z)
        ((∑ i ∈ s, (c i : ℂ) • v i) + Z)).re =
      (∑ i ∈ s, (c i) ^ 2 * m i) + (ClassFunction.inner Z Z).re := by
  classical
  -- `Z` is also orthogonal to each `v i` on the *left*: `⟨v i, Z⟩ = star ⟨Z, v i⟩ = 0`.
  have hZ' : ∀ i ∈ s, ClassFunction.inner (v i) Z = 0 := fun i hi => by
    rw [inner_conj_symm, hZ i hi, star_zero]
  set X : ClassFunction G ℂ := ∑ i ∈ s, (c i : ℂ) • v i with hX
  -- Expand `⟨X + Z, X + Z⟩ = ⟨X, X⟩ + ⟨X, Z⟩ + ⟨Z, X⟩ + ⟨Z, Z⟩`.
  have hXZ : ClassFunction.inner X Z = 0 := by
    rw [hX, inner_sum_left]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [ClassFunction.inner_smul_left, hZ' i hi, mul_zero]
  have hZX : ClassFunction.inner Z X = 0 := by
    rw [inner_conj_symm, hXZ, star_zero]
  -- `⟨X, X⟩ = ∑ i, (c i)² • m i` (the diagonal survives by orthogonality).
  have hXX : ClassFunction.inner X X = ((∑ i ∈ s, (c i) ^ 2 * m i : ℝ) : ℂ) := by
    rw [hX, inner_sum_left, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum_right]
    rw [Finset.sum_eq_single i]
    · rw [ClassFunction.inner_smul_left, inner_smul_right, horth i hi i hi, if_pos rfl,
        Complex.star_def, Complex.conj_ofReal]
      push_cast; ring
    · intro j hj hji
      rw [ClassFunction.inner_smul_left, inner_smul_right, horth i hi j hj,
        if_neg (Ne.symm hji), mul_zero, mul_zero]
    · intro hni; exact absurd hi hni
  rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_add_right, hXZ, hZX, add_zero, zero_add, hXX,
    Complex.add_re, Complex.ofReal_re]

set_option backward.isDefEq.respectTransparency false in
omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- An irreducible representation has positive dimension. -/
theorem finrank_pos_of_isIrreducible {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    0 < Module.finrank ℂ V := by
  have := hρ
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  exact Module.finrank_pos

omit [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- The degree of an irreducible character is a positive integer: `χ(1) = (d : ℂ)` with
`0 < d` (the dimension of the underlying representation). -/
theorem irreducibleCharacter_apply_one_eq_pos_natCast (χ : IrreducibleCharacter G) :
    ∃ d : ℕ, 0 < d ∧ ((χ : ClassFunction G ℂ) : G → ℂ) 1 = (d : ℂ) := by
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
  exact ⟨Module.finrank ℂ V, finrank_pos_of_isIrreducible ρ hρ, by
    rw [congrFun hχ 1, ρ.char_one]⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Norm-2 virtual character is a difference of two distinct irreducible characters.**
If `φ ∈ ZIrr G` has squared norm `2` and vanishes at `1`, then `φ = α - β` for distinct
irreducible characters `α, β`.  This is the layer-2 → layer-3 bridge for Peterfalvi §3
(1.4): each isometric image `τ (χ_i - χ_0)` becomes a named difference of irreducibles. -/
theorem exists_irr_sub_irr_of_inner_self_two {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hnorm : ClassFunction.inner φ φ = 2) (hone : φ (1 : G) = 0) :
    ∃ α β : IrreducibleCharacter G, α ≠ β ∧
      φ = (α : ClassFunction G ℂ) - (β : ClassFunction G ℂ) := by
  classical
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 2 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, β₀, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβ₀ : β₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_pair hαβ] at hrepr
  obtain ⟨dα, hdα, hα1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α₀, hα₀⟩ : IrreducibleCharacter G)
  obtain ⟨dβ, hdβ, hβ1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β₀, hβ₀⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at hα1 hβ1
  have hone' : (c α₀ : ℂ) * (dα : ℂ) + (c β₀ : ℂ) * (dβ : ℂ) = 0 := by
    have h := hone
    rw [hrepr] at h
    simpa only [ClassFunction.add_apply, ClassFunction.smul_apply, hα1, hβ1] using h
  have hdegne : ((dα + dβ : ℕ) : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  rcases hcα with hcα | hcα <;> rcases hcβ with hcβ | hcβ
  · -- (+1, +1): impossible by degree positivity
    exfalso
    rw [hcα, hcβ] at hone'
    simp only [Int.cast_one, one_mul] at hone'
    rw [← Nat.cast_add] at hone'
    exact hdegne hone'
  · -- (+1, -1): φ = α₀ - β₀
    refine ⟨⟨α₀, hα₀⟩, ⟨β₀, hβ₀⟩, fun h => hαβ (congrArg Subtype.val h), ?_⟩
    rw [hrepr, hcα, hcβ]
    simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
    abel
  · -- (-1, +1): φ = β₀ - α₀
    refine ⟨⟨β₀, hβ₀⟩, ⟨α₀, hα₀⟩, fun h => hαβ (congrArg Subtype.val h).symm, ?_⟩
    rw [hrepr, hcα, hcβ]
    simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
    abel
  · -- (-1, -1): impossible by degree positivity
    exfalso
    rw [hcα, hcβ] at hone'
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hone'
    have h2 : (dα : ℂ) + (dβ : ℂ) = 0 := by linear_combination -hone'
    rw [← Nat.cast_add] at h2
    exact hdegne h2

open scoped Classical in
/-- **Bessel's inequality for an orthonormal family of virtual characters**: if `ψ ∈ ZIrr G` has
`‖ψ‖² = N` and `(v i)` is an orthonormal family of virtual characters with integer coefficients
`⟨ψ, v i⟩ = n i`, then `∑ i, (n i)² ≤ N`.  The residual `χ = ψ − ∑ᵢ nᵢ • vᵢ` is a virtual
character orthogonal to every `v i`, so `‖ψ‖² = ∑ᵢ nᵢ² + ‖χ‖²` with `‖χ‖²` a nonnegative
integer (`mem_ZIrr_inner_self_eq_sum_sq`).  This is the norm budget of the Peterfalvi
(10.9)/(11.9.a) grid analyses (`‖∑ aᵢⱼ ω^σ‖² ≤ ‖(μ₀ − ζ)^τ‖²`). -/
theorem sum_sq_inner_le_of_orthonormal {ι : Type*} [Fintype ι]
    {v : ι → ClassFunction G ℂ} (hZ : ∀ i, v i ∈ ZIrr G)
    (horth : ∀ i k, ClassFunction.inner (v i) (v k) = if i = k then (1 : ℂ) else 0)
    {ψ : ClassFunction G ℂ} (hψ : ψ ∈ ZIrr G) {N : ℕ}
    (hψN : ClassFunction.inner ψ ψ = (N : ℂ))
    {n : ι → ℤ} (hn : ∀ i, ClassFunction.inner ψ (v i) = (n i : ℂ)) :
    ∑ i, n i ^ 2 ≤ (N : ℤ) := by
  set X : ClassFunction G ℂ := ∑ i, (n i : ℂ) • v i with hX
  set χ : ClassFunction G ℂ := ψ - X with hχdef
  -- `⟨X, v l⟩ = n l`, hence `⟨χ, v l⟩ = 0`
  have hXvl : ∀ l, ClassFunction.inner X (v l) = (n l : ℂ) := by
    intro l
    rw [hX, inner_sum_left]
    rw [Finset.sum_eq_single l]
    · rw [ClassFunction.inner_smul_left, horth l l, if_pos rfl, mul_one]
    · intro k _ hkl
      rw [ClassFunction.inner_smul_left, horth k l, if_neg hkl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hχvl : ∀ l, ClassFunction.inner χ (v l) = 0 := by
    intro l
    rw [hχdef, ClassFunction.inner_sub_left, hn l, hXvl l, sub_self]
  -- Parseval on `X`
  have hXX : ClassFunction.inner X X = ((∑ i, n i ^ 2 : ℤ) : ℂ) := by
    rw [hX, inner_sum_left]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ClassFunction.inner_smul_left, inner_sum_right]
    rw [Finset.sum_eq_single i]
    · rw [inner_smul_right, horth i i, if_pos rfl, mul_one, star_intCast]; ring
    · intro k _ hki
      rw [inner_smul_right, horth i k, if_neg (fun h => hki h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- the cross terms vanish
  have hχX : ClassFunction.inner χ X = 0 := by
    rw [hX, inner_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, hχvl k, mul_zero]
  have hXχ : ClassFunction.inner X χ = 0 := by
    rw [inner_conj_symm, hχX, star_zero]
  -- `χ` is a virtual character with nonnegative integer squared norm
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    exact Submodule.sum_mem _ fun i _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ (n i) (hZ i)
  have hχZ : χ ∈ ZIrr G := Submodule.sub_mem _ hψ hXZ
  obtain ⟨c, -, -, hcnorm⟩ := mem_ZIrr_inner_self_eq_sum_sq hχZ
  -- assemble over `ℤ`
  have hψeq : ψ = X + χ := by rw [hχdef, add_sub_cancel]
  have hsplit : (N : ℂ) = ((∑ i, n i ^ 2 : ℤ) : ℂ)
      + ((∑ a ∈ c.support, (c a) ^ 2 : ℤ) : ℂ) := by
    rw [← hψN]
    conv_lhs => rw [hψeq]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hXX, hχX, hXχ, hcnorm]
    push_cast
    ring
  have hZeq : (N : ℤ) = (∑ i, n i ^ 2) + ∑ a ∈ c.support, (c a) ^ 2 := by
    exact_mod_cast hsplit
  have hT : 0 ≤ ∑ a ∈ c.support, (c a) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  omega

end OddOrder.RepresentationTheory


