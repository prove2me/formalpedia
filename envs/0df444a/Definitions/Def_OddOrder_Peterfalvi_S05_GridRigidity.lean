-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_GridRigidity
-- name    : OddOrder_Peterfalvi_S05_GridRigidity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:54.806644+00:00
-- url     : https://prove2.me/theorems/2d3952a3-97f1-476c-9f4d-445b1283104c
-- title:
--   Peterfalvi (3.8): abstract norm-2 rigidity for an orthonormal grid family
-- statement:
--   Isolates the module-generic core of Peterfalvi (3.8) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §3, pp. 15-20): rigidity of norm-$2$ virtual characters relative to an orthonormal grid family.
--
--   Main declarations: `orthonormalGrid_diff_rigidity` (Peterfalvi (3.8) rigidity, abstract form).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_GridRigidity.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_GridRigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_GridTrichotomy
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **Norm-`1` support bound** (abstract).  A norm-`1` virtual character `X` (i.e. `X ∈ ±Irr(G)`)
has
at most one nonzero inner product against an orthonormal family `(χ i)` of virtual characters.  By
the norm-`1` classifier `X = ε·μ`; any `χ i` with `⟨X, χ i⟩ ≠ 0` equals `±μ`, and two distinct such
indices would give `⟨χ i, χ i'⟩ = ±1 ≠ 0`, contradicting orthonormality.  Abstract form of
`ncard_inner_chiFam_ne_zero_le_one`. -/
theorem ncard_inner_grid_ne_zero_le_one {Idx : Type*}
    (χ : Idx → ClassFunction G ℂ) (hZ : ∀ i, χ i ∈ ZIrr G)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    (horth_off : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0)
    {X : ClassFunction G ℂ} (hX : X ∈ ZIrr G) (hX1 : ClassFunction.inner X X = 1) :
    {i : Idx | ClassFunction.inner X (χ i) ≠ 0}.ncard ≤ 1 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨ε, μ, hε, hXrepr⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hX hX1
  -- any index in the support has `χ i = ±μ`
  have hkey : ∀ i, ClassFunction.inner X (χ i) ≠ 0 →
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ χ i = δ • (μ : ClassFunction G ℂ) := by
    intro i hi
    obtain ⟨δ, ν, hδ, hνrepr⟩ :=
      exists_zsmul_irreducibleCharacter_of_inner_self_one (hZ i) (horth_diag i)
    refine ⟨δ, hδ, ?_⟩
    have hμν : μ = ν := by
      by_contra hne
      apply hi
      rw [hXrepr, hνrepr, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        irreducibleCharacter_inner_eq_ite, if_neg hne, mul_zero, mul_zero]
    rw [hνrepr, hμν]
  by_cases hempty : {i : Idx | ClassFunction.inner X (χ i) ≠ 0} = ∅
  · rw [hempty]; simp
  · obtain ⟨i₀, hi₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨δ₀, hδ₀, hrepr₀⟩ := hkey i₀ hi₀
    have hsub : {i : Idx | ClassFunction.inner X (χ i) ≠ 0} ⊆ {i₀} := by
      intro i hi
      obtain ⟨δ, hδ, hrepr⟩ := hkey i hi
      have hinner : ClassFunction.inner (χ i) (χ i₀) ≠ 0 := by
        rw [hrepr, hrepr₀, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ,
          ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          irreducibleCharacter_inner_eq_ite, if_pos rfl, star_intCast, mul_one]
        rcases hδ with rfl | rfl <;> rcases hδ₀ with rfl | rfl <;> norm_num
      by_cases heq : i = i₀
      · exact heq
      · exact absurd (horth_off i i₀ heq) hinner
    calc {i : Idx | ClassFunction.inner X (χ i) ≠ 0}.ncard
        ≤ ({i₀} : Set _).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 1 := Set.ncard_singleton i₀

/-- **Norm-`2` support bound** (abstract).  A norm-`2` virtual character `X ∈ ZIrr(G)` has at most
two nonzero inner products against an orthonormal grid family `(χ pq)`.  By the norm-`2`
decomposition `X = ε_α·α + ε_β·β` (`exists_pair_of_sum_sq_eq_two`), each constituent has `≤ 1`
nonzero coefficient (`ncard_inner_grid_ne_zero_le_one`), and the support is contained in
`S_α ∪ S_β`.  Abstract form of `ncard_sigmaCoeff_ne_zero_le_two`. -/
theorem ncard_inner_grid_ne_zero_le_two {Idx : Type*} [Finite Idx]
    (χ : Idx → ClassFunction G ℂ) (hZ : ∀ i, χ i ∈ ZIrr G)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    (horth_off : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0)
    {X : ClassFunction G ℂ} (hX : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2) :
    {i : Idx | ClassFunction.inner X (χ i) ≠ 0}.ncard ≤ 2 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hX
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hX2
  obtain ⟨α, β, hαβ, hs, -, -⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hαZ : α ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨α, hαm⟩ : IrreducibleCharacter G)
  have hβZ : β ∈ ZIrr G := IrreducibleCharacter.mem_ZIrr (⟨β, hβm⟩ : IrreducibleCharacter G)
  have hα1 : ClassFunction.inner α α = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ⟨α, hαm⟩
    rwa [if_pos rfl] at this
  have hβ1 : ClassFunction.inner β β = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ⟨β, hβm⟩
    rwa [if_pos rfl] at this
  have hXαβ : X = (c α : ℂ) • α + (c β : ℂ) • β := by
    rw [hrepr, hs, Finset.sum_pair hαβ]
  refine le_trans (Set.ncard_le_ncard (t :=
    {i | ClassFunction.inner α (χ i) ≠ 0} ∪
    {i | ClassFunction.inner β (χ i) ≠ 0})
    ?_ (Set.toFinite _)) (le_trans (Set.ncard_union_le _ _) ?_)
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    exact hi (by rw [hXαβ, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, hcon.1, hcon.2, mul_zero, mul_zero, add_zero])
  · exact add_le_add
      (ncard_inner_grid_ne_zero_le_one χ hZ horth_diag horth_off hαZ hα1)
      (ncard_inner_grid_ne_zero_le_one χ hZ horth_diag horth_off hβZ hβ1)

/-- **`{0, ±1}` coefficient bound** (abstract).  The inner products of a norm-`2` virtual character
`X ∈ ZIrr(G)` against an orthonormal grid family `(χ pq)` lie in `{0, ±1}`.  Writing
`X = ε_α·α + ε_β·β` and `χ pq = ε·ν` (norm-`1` classifier), the coefficient `⟨X, χ pq⟩` is `ε_α·ε`
if
`ν = α`, `ε_β·ε` if `ν = β`, and `0` otherwise.  Abstract form of
`sigmaCoeff_eq_zero_or_one_of_inner_self_two`. -/
theorem inner_grid_eq_zero_or_pm_one_of_inner_self_two {Idx : Type*}
    (χ : Idx → ClassFunction G ℂ) (hZ : ∀ i, χ i ∈ ZIrr G)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    {X : ClassFunction G ℂ} (hX : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2) (i : Idx) :
    ClassFunction.inner X (χ i) = 0 ∨ ClassFunction.inner X (χ i) = 1 ∨
      ClassFunction.inner X (χ i) = -1 := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hX
  have hsum : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hX2
  obtain ⟨α, β, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two
    (fun a ha => Finsupp.mem_support_iff.mp ha) hsum
  have hαm : α ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβm : β ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  obtain ⟨ε, ν, hε, hν⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one (hZ i)
    (horth_diag i)
  have hαν : ClassFunction.inner α (ν : ClassFunction G ℂ)
      = if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨α, hαm⟩ : IrreducibleCharacter G) ν
  have hβν : ClassFunction.inner β (ν : ClassFunction G ℂ)
      = if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0 :=
    irreducibleCharacter_inner_eq_ite (⟨β, hβm⟩ : IrreducibleCharacter G) ν
  have hf : ClassFunction.inner X (χ i)
      = (c α : ℂ) * ((ε : ℂ) * (if (⟨α, hαm⟩ : IrreducibleCharacter G) = ν then 1 else 0))
        + (c β : ℂ) * ((ε : ℂ) * (if (⟨β, hβm⟩ : IrreducibleCharacter G) = ν then 1 else 0)) := by
    rw [hrepr, hs, Finset.sum_pair hαβ, hν,
      ← Int.cast_smul_eq_zsmul ℂ ε, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hαν, hβν]
  rw [hf]
  by_cases hαe : (⟨α, hαm⟩ : IrreducibleCharacter G) = ν
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · exact absurd (Subtype.ext_iff.mp (hαe.trans hβe.symm)) hαβ
    · rw [if_pos hαe, if_neg hβe]
      simp only [mul_one, mul_zero, add_zero]
      rcases hcα with hcα | hcα <;> rcases hε with hε | hε <;> rw [hcα, hε] <;> norm_num
  · by_cases hβe : (⟨β, hβm⟩ : IrreducibleCharacter G) = ν
    · rw [if_neg hαe, if_pos hβe]
      simp only [mul_one, mul_zero, zero_add]
      rcases hcβ with hcβ | hcβ <;> rcases hε with hε | hε <;> rw [hcβ, hε] <;> norm_num
    · rw [if_neg hαe, if_neg hβe]; left; ring

/-- The difference-grid formula:
`⟨X − s·(χ_{P₁} − χ_{P₂}), χ pq⟩ = ⟨X, χ pq⟩ − s·([P₁=pq] − [P₂=pq])`.
As the family is orthonormal, the `s`-part contributes `∓s` exactly at `P₁, P₂`.  Abstract form of
`sigmaCoeff_sub_smul_chiFam_diff`.  The `if`-indicators use the caller-supplied `[DecidableEq Idx]`,
so that at a concrete grid index `ι × κ` they resolve to the same `instDecidableEqProd` as the
abstract grid lemmas `grid_no_constant_column`/`row`. -/
theorem inner_sub_smul_grid_diff {Idx : Type*} [DecidableEq Idx]
    (χ : Idx → ClassFunction G ℂ)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    (horth_off : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0)
    (X : ClassFunction G ℂ) (s : ℤ) (P1 P2 pq : Idx) :
    ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ pq)
      = ClassFunction.inner X (χ pq)
        - (s : ℂ) * ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) := by
  have h1 : ClassFunction.inner (χ P1) (χ pq) = (if P1 = pq then (1 : ℂ) else 0) := by
    split_ifs with h
    · rw [h, horth_diag]
    · exact horth_off _ _ h
  have h2 : ClassFunction.inner (χ P2) (χ pq) = (if P2 = pq then (1 : ℂ) else 0) := by
    split_ifs with h
    · rw [h, horth_diag]
    · exact horth_off _ _ h
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
    h1, h2]

/-- **All-zero Fourier endgame** (abstract).  If every inner product of
`ψ = X − s·(χ_{P₁} − χ_{P₂})`
against the orthonormal family vanishes (with `‖X‖² = 2`, `P₁ ≠ P₂`, `s = ±1`), then
`X = s·(χ_{P₁} − χ_{P₂})`.  `⟨ψ, χ_{P₁}⟩ = ⟨ψ, χ_{P₂}⟩ = 0` pins `⟨X, χ_{P₁}⟩ = s`,
`⟨X, χ_{P₂}⟩ = −s`; then `‖ψ‖² = ‖X‖² − 2 = 0` (orthonormality, `s² = 1`), so `ψ = 0`.  Abstract
form
of `eq_smul_chiFam_diff_of_all_sigmaCoeff_zero`. -/
theorem eq_smul_grid_diff_of_all_inner_zero {Idx : Type*}
    (χ : Idx → ClassFunction G ℂ)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    (horth_off : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0)
    {X : ClassFunction G ℂ} (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : Idx} (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hall : ∀ i, ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ i) = 0) :
    X = (s : ℂ) • (χ P1 - χ P2) := by
  classical
  have hc1 : ClassFunction.inner X (χ P1) = (s : ℂ) := by
    have he := hall P1
    rw [inner_sub_smul_grid_diff χ horth_diag horth_off X s P1 P2 P1, if_pos rfl,
      if_neg (Ne.symm hPne)] at he
    linear_combination he
  have hc2 : ClassFunction.inner X (χ P2) = -(s : ℂ) := by
    have he := hall P2
    rw [inner_sub_smul_grid_diff χ horth_diag horth_off X s P1 P2 P2, if_neg hPne, if_pos rfl] at he
    linear_combination he
  have h11 : ClassFunction.inner (χ P1) (χ P1) = 1 := horth_diag P1
  have h22 : ClassFunction.inner (χ P2) (χ P2) = 1 := horth_diag P2
  have h12 : ClassFunction.inner (χ P1) (χ P2) = 0 := horth_off P1 P2 hPne
  have h21 : ClassFunction.inner (χ P2) (χ P1) = 0 := horth_off P2 P1 (Ne.symm hPne)
  have hc1' : ClassFunction.inner (χ P1) X = (s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc1, star_intCast]
  have hc2' : ClassFunction.inner (χ P2) X = -(s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc2, star_neg, star_intCast]
  have hsq : (s : ℂ) * (s : ℂ) = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hself : ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2))
      (X - (s : ℂ) • (χ P1 - χ P2)) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hX2, hc1,
      hc2, hc1', hc2', h11, h22, h12, h21, star_intCast]
    linear_combination (-2 : ℂ) * hsq
  have hfin := eq_zero_of_inner_self_re_eq_zero (G := G)
    (φ := X - (s : ℂ) • (χ P1 - χ P2)) (by rw [hself]; simp)
  rwa [sub_eq_zero] at hfin

open scoped Classical in
/-- **Peterfalvi (3.8) rigidity, abstract form** (`eq_signed_sub_cTIiso`, module-generic).  Let
`χ : ι × κ → CF(G)` be an orthonormal family of virtual characters over a rectangular grid whose
sides have coprime odd cardinalities `≥ 3` (the odd-order `w₁ ≠ w₂` gap).  A norm-`2` virtual
character `X ∈ ℤ[Irr G]` whose difference `ψ = X − s·(χ_{P₁} − χ_{P₂})` (`s = ±1`, `P₁ ≠ P₂`) has an
*additively separable* coefficient grid (`hsep`, the (3.7) identity — in applications supplied by
`ψ` vanishing on the regular set `V`) satisfies `X = s·(χ_{P₁} − χ_{P₂})`.

`ψ`'s grid has `NC(ψ) ≤ 4` (`NC(X) ≤ 2` for the norm-`2` `X` plus the two indices `P₁, P₂`).  As the
two side cardinalities are coprime odd `≥ 3`, one of `w₁ + 2 ≤ w₂`, `w₂ + 2 ≤ w₁` holds, so
`NC(ψ) < 2·min(w₁, w₂)` and the (3.8) trichotomy `grid_trichotomy` applies; the constant-column/row
branches are impossible (`grid_no_constant_column`/`row`, using `NC(X) ≤ 2` and coefficients in
`{0, ±1}`), so every coefficient of `ψ` vanishes and `eq_smul_grid_diff_of_all_inner_zero` finishes.
Abstract form of `eq_smul_chiFam_diff_of_vanishOnV`. -/
theorem orthonormalGrid_diff_rigidity {ι κ : Type*} [Finite ι] [Finite κ]
    (χ : ι × κ → ClassFunction G ℂ) (hZ : ∀ pq, χ pq ∈ ZIrr G)
    (horth_diag : ∀ a, ClassFunction.inner (χ a) (χ a) = 1)
    (horth_off : ∀ a b, a ≠ b → ClassFunction.inner (χ a) (χ b) = 0)
    (h3ι : 3 ≤ Nat.card ι) (h3κ : 3 ≤ Nat.card κ)
    (hoddι : Odd (Nat.card ι)) (hoddκ : Odd (Nat.card κ))
    (hcop : Nat.Coprime (Nat.card ι) (Nat.card κ))
    {X : ClassFunction G ℂ} (hXZ : X ∈ ZIrr G) (hX2 : ClassFunction.inner X X = 2)
    {P1 P2 : ι × κ} (hPne : P1 ≠ P2) {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hsep : ∀ (i i' : ι) (j j' : κ),
      ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ (i, j))
          + ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ (i', j'))
        = ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ (i, j'))
          + ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ (i', j))) :
    X = (s : ℂ) • (χ P1 - χ P2) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ι := Fintype.ofFinite _
  have : Fintype κ := Fintype.ofFinite _
  have : Nonempty ι :=
    Fintype.card_pos_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have : Nonempty κ :=
    Fintype.card_pos_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  apply eq_smul_grid_diff_of_all_inner_zero χ horth_diag horth_off hX2 hPne hs
  set a : ι × κ → ℂ :=
    fun pq => ClassFunction.inner (X - (s : ℂ) • (χ P1 - χ P2)) (χ pq) with ha
  set Gr : ι × κ → ℂ := fun pq => ClassFunction.inner X (χ pq) with hGr
  have hae : ∀ pq, a pq = Gr pq
      - (s : ℂ) * ((if P1 = pq then (1 : ℂ) else 0) - (if P2 = pq then (1 : ℂ) else 0)) :=
    fun pq => inner_sub_smul_grid_diff χ horth_diag horth_off X s P1 P2 pq
  have hG2 : {x | Gr x ≠ 0}.ncard ≤ 2 :=
    ncard_inner_grid_ne_zero_le_two χ hZ horth_diag horth_off hXZ hX2
  have hG01 : ∀ x, Gr x = 0 ∨ Gr x = 1 ∨ Gr x = -1 :=
    fun x => inner_grid_eq_zero_or_pm_one_of_inner_self_two χ hZ horth_diag hXZ hX2 x
  have hsc : (s : ℂ) = 1 ∨ (s : ℂ) = -1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hadd : ∀ p p' q q', a (p, q) + a (p', q') = a (p, q') + a (p', q) := hsep
  have hNC4 : {x | a x ≠ 0}.ncard ≤ 4 := by
    have hsub : {x | a x ≠ 0} ⊆ {x | Gr x ≠ 0} ∪ {P1, P2} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, not_not] at hcon
      exact hx (by rw [hae x, hcon.1, if_neg (Ne.symm hcon.2.1), if_neg (Ne.symm hcon.2.2)]; ring)
    have hbpair : ({P1, P2} : Set _).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    calc {x | a x ≠ 0}.ncard ≤ ({x | Gr x ≠ 0} ∪ {P1, P2}).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
      _ ≤ {x | Gr x ≠ 0}.ncard + ({P1, P2} : Set _).ncard := Set.ncard_union_le _ _
      _ ≤ 2 + 2 := add_le_add hG2 hbpair
      _ = 4 := rfl
  have hwne : Nat.card ι ≠ Nat.card κ := by
    intro he; rw [he, Nat.Coprime, Nat.gcd_self] at hcop; omega
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · have hgap : Nat.card ι + 2 ≤ Nat.card κ := by
      obtain ⟨k1, hk1⟩ := hoddι; obtain ⟨k2, hk2⟩ := hoddκ; omega
    have hNClt : {x | a x ≠ 0}.ncard < 2 * Nat.card ι := by omega
    rcases grid_trichotomy a hadd hgap hNClt with hz | ⟨j₀, c, hc, h1, h2⟩ | ⟨i₀, c, hc, h1, h2⟩
    · exact hz
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card]; exact h3ι)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card]; exact h3κ)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc h1 h2).elim
  · set aT : κ × ι → ℂ := fun x => a (x.2, x.1) with haT
    have hgap : Nat.card κ + 2 ≤ Nat.card ι := by
      obtain ⟨k1, hk1⟩ := hoddι; obtain ⟨k2, hk2⟩ := hoddκ; omega
    have haddT : ∀ q q' p p', aT (q, p) + aT (q', p') = aT (q, p') + aT (q', p) :=
      fun q q' p p' => by simp only [haT]; linear_combination hadd p p' q q'
    have hNCltT : {x | aT x ≠ 0}.ncard < 2 * Nat.card κ := by
      have h4 : {x | aT x ≠ 0}.ncard ≤ 4 :=
        le_trans (Set.ncard_le_ncard_of_injOn Prod.swap (fun x hx => hx)
          (Prod.swap_injective.injOn) (Set.toFinite _)) hNC4
      omega
    rcases grid_trichotomy aT haddT hgap hNCltT with hz | ⟨p₀, c, hc, h1, h2⟩ | ⟨q₀, c, hc, h1, h2⟩
    · intro pq; exact hz (pq.2, pq.1)
    · exact (grid_no_constant_row (by rw [← Nat.card_eq_fintype_card]; exact h3κ)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun q => h1 q) (fun i j hi => h2 j i hi)).elim
    · exact (grid_no_constant_column (by rw [← Nat.card_eq_fintype_card]; exact h3ι)
        Gr hG2 hG01 P1 P2 hPne hsc a hae hc (fun p => h1 p) (fun i j hj => h2 j i hj)).elim

end OddOrder.Peterfalvi.S05


