-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
-- name    : OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:04:53.105203+00:00
-- url     : https://prove2.me/theorems/23508d62-64dc-4f72-a0e6-496157ac1653
-- title:
--   Peterfalvi (12.5) without global coherence: pair coherence of equal-degree members
-- statement:
--   Formalizes Peterfalvi (12.5), that a class function orthogonal to $R(\chi)$ for every $\chi \in S$ has constant $\rho$-image on $H - H'$, using only pair coherence of equal-degree members.
--
--   Main declarations: `decomposition_apply_one_pos_natCast` (The degree of a family member is a positive natural); `decomposition_inner_self_card` (Member self-norm); `decomposition_inner_conj_eq_zero` (Peterfalvi (12.2.b) at the member level); `decomposition_ne_conj` (No member of `S` is real ((1.5.e) via the decomposition)).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/PairCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/PairCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- Evaluation of a finite sum of class functions at a point (the eval map is additive). -/
private theorem sum_apply {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) (g : H) : (∑ i ∈ s, F i) g = ∑ i ∈ s, (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

/-- Complex conjugation of a finite sum of class functions (conjugation is additive). -/
private theorem conj_sum {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) : (∑ i ∈ s, F i).conj = ∑ i ∈ s, (F i).conj := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.conj_add, ih]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The degree of a family member is a positive natural:
`χ(1) = ∑_{φ ∈ S(χ)} φ(1)` with each `φ(1)` a positive natural ((12.2.a)). -/
theorem decomposition_apply_one_pos_natCast {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ∃ n : ℕ, 0 < n ∧ chi (1 : ↥L) = (n : ℂ) := by
  have := hyp.finiteG
  classical
  choose d hdpos hd using fun φ : IrreducibleCharacter ↥L =>
    irreducibleCharacter_apply_one_eq_pos_natCast φ
  refine ⟨∑ φ ∈ data.constituents, d φ, ?_, ?_⟩
  · obtain ⟨φ0, hφ0⟩ := data.constituents_nonempty
    exact Finset.sum_pos' (fun φ _ => Nat.zero_le _) ⟨φ0, hφ0, hdpos φ0⟩
  · conv_lhs => rw [data.decomp]
    rw [sum_apply, Nat.cast_sum]
    exact Finset.sum_congr rfl fun φ _ => hd φ

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Member self-norm** ((12.2.a)): `⟨χ, χ⟩ = |S(χ)|` — the multiplicity-one decomposition
into `|S(χ)|` distinct irreducibles. -/
theorem decomposition_inner_self_card {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ClassFunction.inner chi chi = (data.constituents.card : ℂ) := by
  have := hyp.finiteG
  classical
  conv_lhs => rw [data.decomp]
  rw [inner_sum_left]
  have hterm : ∀ φ ∈ data.constituents,
      ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (∑ φ' ∈ data.constituents, (φ' : ClassFunction ↥L ℂ)) = 1 := by
    intro φ hφ
    rw [inner_sum_right,
      Finset.sum_congr rfl fun φ' _ => irreducibleCharacter_inner_eq_ite φ φ',
      Finset.sum_ite_eq data.constituents φ (fun _ => (1 : ℂ)), if_pos hφ]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b) at the member level**: `⟨χ, χ̄⟩ = 0` — no constituent of `χ` is the
conjugate of another (`conj_not_mem`), so the multiplicity-one expansions share no irreducible. -/
theorem decomposition_inner_conj_eq_zero {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ClassFunction.inner chi chi.conj = 0 := by
  have := hyp.finiteG
  classical
  rw [data.decomp, conj_sum, inner_sum_left]
  refine Finset.sum_eq_zero fun φ hφ => ?_
  rw [inner_sum_right]
  refine Finset.sum_eq_zero fun φ' hφ' => ?_
  rw [← IrreducibleCharacter.conjPerm_apply_coe, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  exact data.conj_not_mem φ' hφ' φ hφ
    (by rw [h, IrreducibleCharacter.conjPerm_apply_coe])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- No member of `S` is real ((1.5.e) via the decomposition): `⟨χ, χ⟩ = |S(χ)| ≠ 0` while
`⟨χ, χ̄⟩ = 0`, so `χ ≠ χ̄`. -/
theorem decomposition_ne_conj {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    chi ≠ chi.conj := by
  have := hyp.finiteG
  intro h
  have h0 := decomposition_inner_conj_eq_zero data
  rw [← h, decomposition_inner_self_card data] at h0
  have hcard : data.constituents.card = 0 := by exact_mod_cast h0
  obtain ⟨φ0, hφ0⟩ := data.constituents_nonempty
  rw [Finset.card_eq_zero.mp hcard] at hφ0
  exact absurd hφ0 (Finset.notMem_empty φ0)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (1.5.c) for the type-I family `S`**: distinct members are orthogonal.
Members are inductions `Ind_H^L θ` from the normal `H = L_F`; distinctness of the inductions
means the sources are not `L`-conjugate (`induce_eq_induce_iff_conj`), whence orthogonality
(`inner_induce_eq_zero_of_not_conj`). -/
theorem Sset_pairwise_orthogonal {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (h₁ : χ₁ ∈ hyp.Sset) (h₂ : χ₂ ∈ hyp.Sset) (hne : χ₁ ≠ χ₂) :
    ClassFunction.inner χ₁ χ₂ = 0 := by
  have := hyp.finiteG
  classical
  have hnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨θ₁, -, hχ₁eq⟩ := h₁
  obtain ⟨θ₂, -, hχ₂eq⟩ := h₂
  rw [hχ₁eq, hχ₂eq]
  refine inner_induce_eq_zero_of_not_conj θ₁ θ₂ fun g hg => hne ?_
  rw [hχ₁eq, hχ₂eq]
  exact (induce_eq_induce_iff_conj θ₁ θ₂).mpr ⟨g, hg⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Cross-block orthogonality of the (12.2.b) blocks**: for constituents `φ ∈ S(χ₁)`,
`φ′ ∈ S(χ₂)` (over the same `hyp`, possibly `χ₁ = χ₂`) with `φ, φ′` distinct and non-conjugate,
the orthonormal blocks `R₁(φ)` and `R₁(φ′)` are orthogonal.  The (4.1) reduction
(`toOrthonormalImage_inner_eq_zero_across`) sends `⟨α, β⟩` to the signed-difference orthogonality
`⟨(φ − φ̄)^τ, (φ′ − φ̄′)^τ⟩ = 0` (`constituentDiff_tau_inner_eq_zero_of_ne_across`). -/
theorem R1_orthogonal_of_ne {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data1.constituents)
    (hφ' : φ' ∈ data2.constituents) (hne : φ ≠ φ')
    (h2 : φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ')
    (h3 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ') :
    ∀ α ∈ (R1 data1 hφ).imageSet, ∀ β ∈ (R1 data2 hφ').imageSet,
      ClassFunction.inner α β = 0 := by
  intro α hα β hβ
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ) (R1cdi data2 hφ') ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data2 hφ')]
  exact constituentDiff_tau_inner_eq_zero_of_ne_across data1 data2 hφ hφ' hne h2 h3

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The non-conjugacy conditions of `R1_orthogonal_of_ne` for two **distinct constituents of
decompositions over the same `hyp`**, derived from `conj_not_mem`: `φ ≠ φ̄′` and `φ̄ ≠ φ′`. -/
theorem constituents_ne_conj {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data1.constituents)
    (hφ' : φ' ∈ data2.constituents)
    (hcc : ∀ ψ ∈ data2.constituents,
      (ψ : ClassFunction ↥L ℂ).conj ≠ (φ : ClassFunction ↥L ℂ))
    (hcc' : ∀ ψ ∈ data1.constituents,
      (ψ : ClassFunction ↥L ℂ).conj ≠ (φ' : ClassFunction ↥L ℂ)) :
    φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' ∧
      OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ' := by
  have := hyp.finiteG
  constructor
  · intro h
    exact hcc φ' hφ'
      (by rw [h, OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter])
  · intro h
    exact hcc' φ hφ
      (by rw [← h, OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter])

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), bundled**: `R(χ)` as an `OrthonormalCharacterImageFamily` — the finset
`⋃_{φ ∈ S(χ)} R₁(φ)` with `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α`.  Orthonormality within a block is the
`R₁(φ)` field; across blocks it is `R1_orthogonal_of_ne` (whose orthogonality also forces the
blocks disjoint, giving the `biUnion` sum decomposition of the image equation). -/
noncomputable def RsetImageFamily {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      hyp.tau chi where
  imageSet := data.constituents.attach.biUnion fun φ => (R1 data φ.2).imageSet
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_biUnion] at hα
    obtain ⟨φ, -, hα⟩ := hα
    exact (R1 data φ.2).mem_ZIrr α hα
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_biUnion] at hα hβ
    obtain ⟨φ, -, hα⟩ := hα
    obtain ⟨φ', -, hβ⟩ := hβ
    by_cases hblock : φ = φ'
    · subst hblock
      exact (R1 data φ.2).orthonormal α hα β hβ
    · have hne : (φ : IrreducibleCharacter ↥L) ≠ (φ' : IrreducibleCharacter ↥L) :=
        fun h => hblock (Subtype.ext h)
      obtain ⟨h2, h3⟩ := constituents_ne_conj data data φ.2 φ'.2
        (fun ψ hψ => data.conj_not_mem ψ hψ φ.1 φ.2)
        (fun ψ hψ => data.conj_not_mem ψ hψ φ'.1 φ'.2)
      have h0 := R1_orthogonal_of_ne data data φ.2 φ'.2 hne h2 h3 α hα β hβ
      have hαβ : α ≠ β := by
        rintro rfl
        have h1 := (R1 data φ.2).inner_self_of_mem hα
        rw [h0] at h1
        exact one_ne_zero h1.symm
      rw [if_neg hαβ]
      exact h0
  image_eq := by
    have hdisj : ∀ x ∈ data.constituents.attach, ∀ y ∈ data.constituents.attach, x ≠ y →
        Disjoint ((R1 data x.2).imageSet) ((R1 data y.2).imageSet) := by
      rintro x - y - hxy
      rw [Finset.disjoint_left]
      intro α hαx hαy
      have hne : (x : IrreducibleCharacter ↥L) ≠ (y : IrreducibleCharacter ↥L) :=
        fun h => hxy (Subtype.ext h)
      obtain ⟨h2, h3⟩ := constituents_ne_conj data data x.2 y.2
        (fun ψ hψ => data.conj_not_mem ψ hψ x.1 x.2)
        (fun ψ hψ => data.conj_not_mem ψ hψ y.1 y.2)
      have h0 := R1_orthogonal_of_ne data data x.2 y.2 hne h2 h3 α hαx α hαy
      have h1 := (R1 data x.2).inner_self_of_mem hαx
      rw [h0] at h1
      exact one_ne_zero h1.symm
    have hsplit : chi - chi.conj
        = ∑ φ ∈ data.constituents.attach,
            (((φ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ)
              - ((φ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ).conj) := by
      rw [Finset.sum_attach data.constituents
        (fun φ : IrreducibleCharacter ↥L =>
          ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj)),
        Finset.sum_sub_distrib, ← conj_sum, ← data.decomp]
    rw [hsplit, map_sum, Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun φ _ => (R1 data φ.2).image_eq

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The bundled image set is exactly `R(χ) = Rset data` (as a membership equivalence). -/
theorem mem_RsetImageFamily_iff {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {α : ClassFunction G ℂ} :
    α ∈ (RsetImageFamily data).imageSet ↔ α ∈ Rset data := by
  constructor
  · intro hα
    rw [show (RsetImageFamily data).imageSet
        = data.constituents.attach.biUnion (fun φ => (R1 data φ.2).imageSet) from rfl,
      Finset.mem_biUnion] at hα
    obtain ⟨φ, -, hα⟩ := hα
    exact ⟨φ.1, φ.2, hα⟩
  · rintro ⟨φ, hφ, hα⟩
    rw [show (RsetImageFamily data).imageSet
        = data.constituents.attach.biUnion (fun φ => (R1 data φ.2).imageSet) from rfl,
      Finset.mem_biUnion]
    exact ⟨⟨φ, hφ⟩, Finset.mem_attach _ _, hα⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- A family member is a virtual character: `χ = ∑_{φ ∈ S(χ)} φ ∈ ℤ[Irr L]`. -/
theorem decomposition_mem_ZIrr {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    chi ∈ ZIrr ↥L := by
  have := hyp.finiteG
  rw [data.decomp]
  exact Submodule.sum_mem _ fun φ _ => φ.mem_ZIrr

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The conjugate member has the same degree: `χ̄(1) = χ(1)` (the degree is a natural). -/
theorem decomposition_conj_apply_one {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    chi.conj (1 : ↥L) = chi (1 : ↥L) := by
  have := hyp.finiteG
  obtain ⟨n, -, hn⟩ := decomposition_apply_one_pos_natCast data
  rw [ClassFunction.conj_apply, hn, star_natCast]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Cross-member constituent distinctness from orthogonality**: `⟨χ₁, χ₂⟩ = 0` forces the
multiplicity-one constituent sets apart — no `φ ∈ S(χ₁)` equals a `φ′ ∈ S(χ₂)` (a shared
irreducible would contribute `1` to the inner product). -/
theorem constituents_ne_of_inner_eq_zero {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    (h : ClassFunction.inner chi1 chi2 = 0) :
    ∀ φ₁ ∈ data1.constituents, ∀ φ₂ ∈ data2.constituents, φ₁ ≠ φ₂ := by
  have := hyp.finiteG
  classical
  have hcount : ClassFunction.inner chi1 chi2
      = ((data1.constituents.filter (· ∈ data2.constituents)).card : ℂ) := by
    conv_lhs => rw [data1.decomp, data2.decomp]
    rw [inner_sum_left]
    have hterm : ∀ φ₁ ∈ data1.constituents,
        ClassFunction.inner (φ₁ : ClassFunction ↥L ℂ)
          (∑ φ₂ ∈ data2.constituents, (φ₂ : ClassFunction ↥L ℂ))
          = if φ₁ ∈ data2.constituents then (1 : ℂ) else 0 := by
      intro φ₁ _
      rw [inner_sum_right,
        Finset.sum_congr rfl fun φ₂ _ => irreducibleCharacter_inner_eq_ite φ₁ φ₂,
        Finset.sum_ite_eq data2.constituents φ₁ fun _ => (1 : ℂ)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  rw [h] at hcount
  have hcard : (data1.constituents.filter (· ∈ data2.constituents)).card = 0 := by
    exact_mod_cast hcount.symm
  intro φ₁ h1 φ₂ h2 heq
  subst heq
  have hmem : φ₁ ∈ data1.constituents.filter (· ∈ data2.constituents) :=
    Finset.mem_filter.mpr ⟨h1, h2⟩
  rw [Finset.card_eq_zero.mp hcard] at hmem
  exact absurd hmem (Finset.notMem_empty φ₁)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Cross-member conjugate-distinctness from orthogonality to the conjugate**:
`⟨χ₁, χ̄₂⟩ = 0` forces `φ₁ ≠ φ̄₂` for all constituents `φ₁ ∈ S(χ₁)`, `φ₂ ∈ S(χ₂)`
(a conjugate match would contribute `1`). -/
theorem constituents_not_conj_of_inner_conj_eq_zero {L : Subgroup G} [Finite G]
    {hyp : Hypothesis L} {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    (h : ClassFunction.inner chi1 chi2.conj = 0) :
    ∀ φ₁ ∈ data1.constituents, ∀ φ₂ ∈ data2.constituents,
      (φ₁ : ClassFunction ↥L ℂ) ≠ (φ₂ : ClassFunction ↥L ℂ).conj := by
  have := hyp.finiteG
  classical
  have hinv : ∀ ψ : IrreducibleCharacter ↥L,
      IrreducibleCharacter.conjPerm ↥L (IrreducibleCharacter.conjPerm ↥L ψ) = ψ := fun ψ =>
    IrreducibleCharacter.ext (by
      rw [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.conjPerm_apply_coe,
        ClassFunction.conj_conj])
  have hcount : ClassFunction.inner chi1 chi2.conj
      = ((data1.constituents.filter
          (fun φ₁ => IrreducibleCharacter.conjPerm ↥L φ₁ ∈ data2.constituents)).card : ℂ) := by
    conv_lhs => rw [data1.decomp, data2.decomp]
    rw [conj_sum, inner_sum_left]
    have hterm : ∀ φ₁ ∈ data1.constituents,
        ClassFunction.inner (φ₁ : ClassFunction ↥L ℂ)
          (∑ φ₂ ∈ data2.constituents, ((φ₂ : ClassFunction ↥L ℂ)).conj)
          = if IrreducibleCharacter.conjPerm ↥L φ₁ ∈ data2.constituents then (1 : ℂ) else 0 := by
      intro φ₁ _
      rw [inner_sum_right]
      have hterm2 : ∀ φ₂ ∈ data2.constituents,
          ClassFunction.inner (φ₁ : ClassFunction ↥L ℂ) ((φ₂ : ClassFunction ↥L ℂ)).conj
            = if φ₂ = IrreducibleCharacter.conjPerm ↥L φ₁ then (1 : ℂ) else 0 := by
        intro φ₂ _
        rw [← IrreducibleCharacter.conjPerm_apply_coe, irreducibleCharacter_inner_eq_ite]
        refine if_congr ⟨fun hc => ?_, fun hc => ?_⟩ rfl rfl
        · rw [hc, hinv]
        · rw [hc, hinv]
      rw [Finset.sum_congr rfl hterm2,
        Finset.sum_ite_eq' data2.constituents (IrreducibleCharacter.conjPerm ↥L φ₁)
          fun _ => (1 : ℂ)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  rw [h] at hcount
  have hcard : (data1.constituents.filter
      (fun φ₁ => IrreducibleCharacter.conjPerm ↥L φ₁ ∈ data2.constituents)).card = 0 := by
    exact_mod_cast hcount.symm
  intro φ₁ h1 φ₂ h2 heq
  have hφeq : φ₁ = IrreducibleCharacter.conjPerm ↥L φ₂ := IrreducibleCharacter.ext (by
    rw [IrreducibleCharacter.conjPerm_apply_coe]; exact heq)
  have hmem : φ₁ ∈ data1.constituents.filter
      (fun φ₁ => IrreducibleCharacter.conjPerm ↥L φ₁ ∈ data2.constituents) :=
    Finset.mem_filter.mpr ⟨h1, by rw [hφeq, hinv]; exact h2⟩
  rw [Finset.card_eq_zero.mp hcard] at hmem
  exact absurd hmem (Finset.notMem_empty φ₁)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Inclusion form of `Sset_diff_support_subset_ambientA`** for a general (non-Frobenius)
type-`I` maximal: the difference of equal-degree members is supported in `A(L)`, needing only
`H^# ⊆ A(L)` (`sharpSubgroup_H_subset_typeIA`), not the Frobenius equality `A(L) = H^#`. -/
theorem Sset_diff_support_subset_ambientA_of_sharp_subset {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA) :
    (χ₁ - χ₂).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hnot : ¬((x : G) ∉ hyp.H ∨ x = 1) := fun h =>
    hx (Sset_diff_vanishes_off_H_sharp hyp hχ₁ hχ₂ hdeg h)
  push Not at hnot
  exact hsub ⟨hnot.1, fun h1 => hnot.2 (Subtype.ext h1)⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5), `R(χ)`-family form**: for a coherent subfamily `S ∋ χ, χ̄` (with the
member `χ` of the (12.1) family carrying its (12.2) decomposition), the coherent image
`χ^ν = coh.extension χ` lies in `ℤ[R(χ)]`.

Norm-general: the `ofProjection (ψ := 0)` engine is applied against the full block family
`R(χ) = RsetImageFamily data` (of cardinality `2·|S(χ)|`), so `χ` need not be irreducible —
this is the (5.5) step of the Coq `mem_coherent_sum_subseq` route.  The subfamily-lattice
inputs are: `χ, χ̄ ∈ S`, and `(χ − χ̄)` supported in the Dade domain. -/
theorem coherent_extension_mem_span_Rset_of_mem {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) {S : Set (ClassFunction ↥L ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S hyp.A)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    (hchiS : chi ∈ S) (hchiConjS : chi.conj ∈ S)
    (hsupp : (chi - chi.conj).support ⊆ hyp.A) :
    coh.extension chi ∈ Submodule.span ℤ (Rset data) := by
  have := hyp.finiteG
  classical
  have hchi_zSpan : chi ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) S :=
    Submodule.subset_span hchiS
  have hchibar_zSpan : chi.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) S :=
    Submodule.subset_span hchiConjS
  have hdiff_zSpan : chi - chi.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥L) S :=
    Submodule.sub_mem _ hchi_zSpan hchibar_zSpan
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥L) {chi - chi.conj, chi - 0} ≤
      OddOrder.Peterfalvi.S07.zSpan (L := ↥L) S := by
    change Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hchi_zSpan
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0)
        (RsetImageFamily data) coh.extension
        (fun φ ζ hφ hζ => coh.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (coh.extends_on_supported (chi - chi.conj) ⟨hdiff_zSpan, hsupp⟩)
        (by rw [sub_zero]; exact coh.extension_mem_ZIrr _ hchi_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        (decomposition_inner_conj_eq_zero data))
  have hgoal : coh.extension chi = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα =>
    Submodule.subset_span ((mem_RsetImageFamily_iff data).mp (hEsub hα))

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5) step, via (12.2) + (5.7) + (5.5)** (Coq `pair_degree_coherence` +
`mem_coherent_sum_subseq`): for equal-degree members `χ₁, χ₂ ∈ S`,
`(χ₁ − χ₂)^τ ∈ ℤ[R(χ₁) ∪ R(χ₂)]`.

The quadruple `{χ₁, χ̄₁, χ₂, χ̄₂}` is a uniform-degree conjugate-closed pairwise-orthogonal
family ((1.5.c) `Sset_pairwise_orthogonal`), so it is coherent
(`uniform_degree_coherence_of_families`, the (5.7) engine); `τ` agrees with the coherent
extension on the `A(L)`-supported difference `χ₁ − χ₂`, and (5.5)
(`coherent_extension_mem_span_Rset_of_mem`) puts each image in its `ℤ[R(χᵢ)]`.  The
degenerate cases `χ₂ = χ₁` (zero) and `χ₂ = χ̄₁` (the (12.2.b) image equation) are direct. -/
theorem pair_tau_diff_mem_span {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA)
    (h1A : (1 : G) ∉ hyp.ambientA)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (h₁ : χ₁ ∈ hyp.Sset) (h₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L)) :
    hyp.tau (χ₁ - χ₂) ∈
      Submodule.span ℤ (Rset (data χ₁ h₁) ∪ Rset (data χ₂ h₂)) := by
  have := hyp.finiteG
  classical
  by_cases heq : χ₁ = χ₂
  · have h0 : χ₁ - χ₂ = 0 := by rw [heq, sub_self]
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  by_cases hconj : χ₂ = χ₁.conj
  · subst hconj
    rw [(RsetImageFamily (data χ₁ h₁)).image_eq]
    exact Submodule.sum_mem _ fun α hα =>
      Submodule.subset_span
        (Set.mem_union_left _ ((mem_RsetImageFamily_iff (data χ₁ h₁)).mp hα))
  -- the generic quadruple case
  set Squad : Set (ClassFunction ↥L ℂ) := {χ₁, χ₁.conj, χ₂, χ₂.conj} with hSquad
  -- membership of the quadruple in `S`, and the member data
  have hmemS : ∀ a ∈ Squad, a ∈ hyp.Sset := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact h₁
    · exact (Sset_closedUnderConjugate hyp) h₁
    · exact h₂
    · exact (Sset_closedUnderConjugate hyp) h₂
  -- distinctness pins
  have hne1c : χ₁ ≠ χ₁.conj := decomposition_ne_conj (data χ₁ h₁)
  have hne2c : χ₂ ≠ χ₂.conj := decomposition_ne_conj (data χ₂ h₂)
  have hne1c2 : χ₁.conj ≠ χ₂ := fun h => hconj h.symm
  have hne12c : χ₁ ≠ χ₂.conj := fun h => hconj (by rw [h, ClassFunction.conj_conj])
  have hne1c2c : χ₁.conj ≠ χ₂.conj := fun h =>
    heq (by rw [← ClassFunction.conj_conj χ₁, h, ClassFunction.conj_conj])
  -- degrees: every member of the quadruple has degree `χ₁(1)`
  have hdegQ : ∀ a ∈ Squad, a (1 : ↥L) = χ₁ (1 : ↥L) := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl
    · rfl
    · exact decomposition_conj_apply_one (data χ₁ h₁)
    · exact hdeg.symm
    · rw [decomposition_conj_apply_one (data χ₂ h₂)]
      exact hdeg.symm
  -- supports: differences of quadruple members are `A(L)`-supported
  have hsuppQ : ∀ a ∈ Squad, ∀ b ∈ Squad, ((a - b : ClassFunction ↥L ℂ)).support ⊆ hyp.A := by
    intro a ha b hb
    exact Sset_diff_support_subset_ambientA_of_sharp_subset hyp (hmemS a ha) (hmemS b hb)
      ((hdegQ a ha).trans (hdegQ b hb).symm) hsub
  -- (5.7): the quadruple is coherent
  have hcohQ : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau Squad hyp.A) := by
    refine OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
      (Set.Finite.insert χ₁ (Set.Finite.insert χ₁.conj (Set.Finite.insert χ₂
        (Set.finite_singleton χ₂.conj))))
      (Set.mem_insert _ _)
      (fun η hη => RsetImageFamily (data η (hmemS η hη)))
      (fun a ha b hb hab => Sset_pairwise_orthogonal hyp (hmemS a ha) (hmemS b hb) hab)
      ?_ ?_ ⟨(data χ₁ h₁).constituents.card, decomposition_inner_self_card (data χ₁ h₁)⟩
      ?_ ?_ ?_ ?_ (hdegQ) ?_ ?_ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Ne.symm hne1c)
    · -- conjugation closure
      intro a ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [ClassFunction.conj_conj]; exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      · rw [ClassFunction.conj_conj]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · -- no real members
      intro a ha
      exact decomposition_ne_conj (data a (hmemS a ha))
    · -- the Dade isometry on the supported span
      intro φ ζ hφ hζ
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        hyp.dadeData.dade (S := {φ, ζ})
        (by
          rintro s (rfl | hs)
          · exact hφ.2
          · rw [Set.mem_singleton_iff] at hs; subst hs; exact hζ.2)
        (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
    · -- τ-images of differences are virtual characters
      intro a ha b hb
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        hyp.dadeData.dade (hsuppQ a ha b hb)
        (Submodule.sub_mem _ (decomposition_mem_ZIrr (data a (hmemS a ha)))
          (decomposition_mem_ZIrr (data b (hmemS b hb))))
    · -- supports of differences
      exact hsuppQ
    · -- (5.2.e) cross-orthogonality of the `R`-families
      intro φ ξ hφ hξ hinner hinnerc α hα β hβ
      rw [mem_RsetImageFamily_iff] at hα hβ
      obtain ⟨φc, hφc, hα⟩ := hα
      obtain ⟨ξc, hξc, hβ⟩ := hβ
      have hnecs := constituents_ne_of_inner_eq_zero (data φ (hmemS φ hφ))
        (data ξ (hmemS ξ hξ)) hinner φc hφc ξc hξc
      have hnconj := constituents_not_conj_of_inner_conj_eq_zero (data φ (hmemS φ hφ))
        (data ξ (hmemS ξ hξ)) hinnerc
      obtain ⟨hc2, hc3⟩ := constituents_ne_conj (data φ (hmemS φ hφ)) (data ξ (hmemS ξ hξ))
        hφc hξc
        (fun ψ hψ hcon => hnconj φc hφc ψ hψ hcon.symm)
        (fun ψ hψ hcon => hnconj ψ hψ ξc hξc (by
          rw [← ClassFunction.conj_conj (ψ : ClassFunction ↥L ℂ), hcon]))
      exact R1_orthogonal_of_ne _ _ hφc hξc hnecs hc2 hc3 α hα β hβ
    · -- nonzero degree
      obtain ⟨n, hnpos, hn⟩ := decomposition_apply_one_pos_natCast (data χ₁ h₁)
      rw [hn]
      exact_mod_cast hnpos.ne'
    · -- `1 ∉ A`
      intro h1
      have hmem : ((1 : ↥L) : G) ∈ hyp.ambientA := h1
      rw [OneMemClass.coe_one] at hmem
      exact h1A hmem
  obtain ⟨coh⟩ := hcohQ
  -- (5.5) on each of `χ₁`, `χ₂`
  have hmem₁ : χ₁ ∈ Squad := Set.mem_insert _ _
  have hmem₁c : χ₁.conj ∈ Squad := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hmem₂ : χ₂ ∈ Squad := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert _ _))
  have hmem₂c : χ₂.conj ∈ Squad := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have e₁ : coh.extension χ₁ ∈ Submodule.span ℤ (Rset (data χ₁ h₁)) :=
    coherent_extension_mem_span_Rset_of_mem hyp coh (data χ₁ h₁) hmem₁ hmem₁c
      (hsuppQ χ₁ hmem₁ χ₁.conj hmem₁c)
  have e₂ : coh.extension χ₂ ∈ Submodule.span ℤ (Rset (data χ₂ h₂)) :=
    coherent_extension_mem_span_Rset_of_mem hyp coh (data χ₂ h₂) hmem₂ hmem₂c
      (hsuppQ χ₂ hmem₂ χ₂.conj hmem₂c)
  -- `τ` agrees with the coherent extension on the supported difference
  have hτdiff : hyp.tau (χ₁ - χ₂) = coh.extension χ₁ - coh.extension χ₂ := by
    rw [← map_sub]
    exact (coh.extends_on_supported (χ₁ - χ₂)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hmem₁) (Submodule.subset_span hmem₂),
        hsuppQ χ₁ hmem₁ χ₂ hmem₂⟩).symm
  rw [hτdiff]
  exact Submodule.sub_mem _
    (Submodule.span_mono Set.subset_union_left e₁)
    (Submodule.span_mono Set.subset_union_right e₂)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), the `o_rpsi_S` coefficient equality — coherence-free form.**  The
`ρ`-image `ψ^ρ = toHypothesis71.chiRhoCF ψ` has the *same* coefficient on two equal-degree
members `χ₁, χ₂ ∈ S`, with the orthogonality hypothesis in `R(χ)`-form (as in the original
text): `⟨χ₁ − χ₂, ρψ⟩ = ⟨(χ₁ − χ₂)^τ, ψ⟩` (`chiRho_adjoint` reciprocity), and
`(χ₁ − χ₂)^τ ∈ ℤ[R(χ₁) ∪ R(χ₂)] ⊥ ψ` (`pair_tau_diff_mem_span` + `horth`).

The coherence-free replacement of `chiRhoCF_inner_eq_of_equal_degree` for the (12.15)
application, where the maximal `M` is not a Frobenius group and carries no family coherence. -/
theorem chiRhoCF_inner_eq_of_equal_degree_ofData {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA)
    (h1A : (1 : G) ∉ hyp.ambientA) {ψ : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner ψ α = 0)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L)) :
    ClassFunction.inner χ₁ (hyp.toHypothesis71.chiRhoCF ψ)
      = ClassFunction.inner χ₂ (hyp.toHypothesis71.chiRhoCF ψ) := by
  have := hyp.finiteG
  have hsupp := Sset_diff_support_subset_ambientA_of_sharp_subset hyp hχ₁ hχ₂ hdeg hsub
  set α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typeIA L hyp.typeI) L :=
    ⟨χ₁ - χ₂, (ClassFunction.mem_supportedSubmodule).mpr hsupp⟩ with hα
  have hkey : ClassFunction.inner (χ₁ - χ₂) (hyp.toHypothesis71.chiRhoCF ψ) = 0 := by
    have hrec := hyp.toHypothesis71.chiRho_adjoint α ψ
    have hαcoe : (α : ClassFunction ↥L ℂ) = χ₁ - χ₂ := rfl
    rw [hαcoe] at hrec
    have h0 : ClassFunction.inner ψ (hyp.tau (χ₁ - χ₂)) = 0 :=
      OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan
        (fun β hβ => by
          rcases hβ with hβ | hβ
          · exact horth χ₁ hχ₁ β hβ
          · exact horth χ₂ hχ₂ β hβ)
        (pair_tau_diff_mem_span hyp data hsub h1A hχ₁ hχ₂ hdeg)
    rw [← hrec, hyp.toHypothesis71_tau_apply α, hαcoe,
      inner_conj_symm ψ (hyp.tau (χ₁ - χ₂)), h0, star_zero]
  rw [ClassFunction.inner_sub_left] at hkey
  exact sub_eq_zero.mp hkey

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), the θ-level coefficient equality — coherence-free form** (Frobenius
reciprocity applied to `chiRhoCF_inner_eq_of_equal_degree_ofData`): for `χᵢ = Ind_H^L θᵢ ∈ S`
of equal degree, `⟨θ₁, Res_H ρψ⟩ = ⟨θ₂, Res_H ρψ⟩`. -/
theorem chiRhoCF_restrict_inner_eq_of_equal_degree_ofData {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA)
    (h1A : (1 : G) ∉ hyp.ambientA) {ψ : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner ψ α = 0)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L))
    {θ₁ θ₂ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ}
    (hθ₁ : χ₁ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ₁)
    (hθ₂ : χ₂ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) θ₂) :
    ClassFunction.inner θ₁ (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ))
      = ClassFunction.inner θ₂ (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ)) := by
  have := hyp.finiteG
  have hfact := chiRhoCF_inner_eq_of_equal_degree_ofData hyp data hsub h1A horth hχ₁ hχ₂ hdeg
  rw [hθ₁, hθ₂, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict] at hfact
  exact hfact

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5), coherence-free**: for `ψ ∈ CF(G)` orthogonal to every family block
(`ψ ⊥ R(χ)` for all `χ ∈ S`, in `Rset` form as in the original text), the restriction of the
`ρ`-image to `H` is **constant on `H − H′`**.

The coherence-free counterpart of `chiRhoCF_restrict_constant_off_derived`, for the (12.15)
application to the counterexample maximal `M` (not a Frobenius group, no family coherence):
same assembly — Clifford (1.7.b) blocks (`commutator_induce_constituents_apply_one_eq` /
`inner_induce_constituent_eq_of_apply_one_eq`) and the `DpsiH` span core
(`constant_off_normal_of_inner_block_const`) — with the coefficient equality supplied by the
pair-coherence route (`chiRhoCF_restrict_inner_eq_of_equal_degree_ofData`). -/
theorem chiRhoCF_restrict_constant_off_derived_ofData {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA)
    (h1A : (1 : G) ∉ hyp.ambientA) {ψ : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner ψ α = 0)
    {x y : ↥((hyp.typeI.typeF.H).subgroupOf L)}
    (hx : x ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L))
    (hy : y ∉ commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) :
    ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ) x
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (hyp.toHypothesis71.chiRhoCF ψ) y := by
  have := hyp.finiteG
  classical
  set Hc := ((hyp.typeI.typeF.H).subgroupOf L) with hHc
  set g : ClassFunction ↥Hc ℂ :=
    ClassFunction.restrict Hc (hyp.toHypothesis71.chiRhoCF ψ) with hg
  have : Fintype ↥(commutator ↥Hc) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(commutator ↥Hc) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (IrreducibleCharacter ↥Hc) := Fintype.ofFinite _
  refine OddOrder.RepresentationTheory.constant_off_normal_of_inner_block_const g
    (fun θ₁ θ₂ ρ hθ₁t hθ₂t hlo₁ hlo₂ => ?_) (fun θ₁ θ₂ ρ hlo₁ hlo₂ => ?_) hx hy
  · -- Block-constant coefficients on the non-trivial constituents.
    have hdegθ : (θ₁ : ClassFunction ↥Hc ℂ) 1 = (θ₂ : ClassFunction ↥Hc ℂ) 1 :=
      OddOrder.RepresentationTheory.commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo₁ hlo₂
    have hχ₁ : ClassFunction.induce Hc (θ₁ : ClassFunction ↥Hc ℂ) ∈ hyp.Sset := ⟨θ₁, hθ₁t, rfl⟩
    have hχ₂ : ClassFunction.induce Hc (θ₂ : ClassFunction ↥Hc ℂ) ∈ hyp.Sset := ⟨θ₂, hθ₂t, rfl⟩
    have hdegχ : ClassFunction.induce Hc (θ₁ : ClassFunction ↥Hc ℂ) (1 : ↥L)
        = ClassFunction.induce Hc (θ₂ : ClassFunction ↥Hc ℂ) (1 : ↥L) := by
      rw [ClassFunction.induce_apply_one, ClassFunction.induce_apply_one, hdegθ]
    have h := chiRhoCF_restrict_inner_eq_of_equal_degree_ofData hyp data hsub h1A horth
      hχ₁ hχ₂ hdegχ rfl rfl
    rw [ClassFunction.inner_star_comm g (θ₁ : ClassFunction ↥Hc ℂ),
      ClassFunction.inner_star_comm g (θ₂ : ClassFunction ↥Hc ℂ), h]
  · -- Block-constant multiplicities.
    have hdegθ : (θ₁ : ClassFunction ↥Hc ℂ) 1 = (θ₂ : ClassFunction ↥Hc ℂ) 1 :=
      OddOrder.RepresentationTheory.commutator_induce_constituents_apply_one_eq ρ θ₁ θ₂ hlo₁ hlo₂
    exact OddOrder.RepresentationTheory.inner_induce_constituent_eq_of_apply_one_eq
      hlo₁ hlo₂ hdegθ

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), the constancy composition**: `ψ` itself is constant on `H − H′` — the
(12.5) conclusion for the `ρ`-image (`chiRhoCF_restrict_constant_off_derived_ofData`) transferred
to `ψ` by the (12.15) first claim `ψ^ρ(g) = ψ(g)` on `H^#`, taken here as the hypothesis
`heval` (the `H(g)`-case-split evaluation, (8.13)-supplied by the caller).

The `g ∉ H′` membership forces `g ≠ 1` (`1 ∈ H′`), so `heval` is only ever invoked on `H^#`.
Instantiated at the counterexample `M` (`H = M_F = K`), this is exactly the "`ψ` is constant on
`K − K′`" clause of (12.15), the `hconst` input of `rhoM_integer_values`. -/
theorem psi_constant_on_kernel_sub_derived_ofData {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    (hsub : sharpSubgroup hyp.typeI.typeF.H ⊆ hyp.ambientA)
    (h1A : (1 : G) ∉ hyp.ambientA) {ψ : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner ψ α = 0)
    (heval : ∀ g : G, ∀ hg : g ∈ hyp.typeI.typeF.H, g ≠ 1 →
      hyp.toHypothesis71.chiRhoCF ψ (⟨g, hyp.typeI.typeF.H_le hg⟩ : ↥L) = ψ g)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ hyp.typeI.typeF.H) (hg₁' : g₁ ∉ derivedInG hyp.typeI.typeF.H)
    (hg₂ : g₂ ∈ hyp.typeI.typeF.H) (hg₂' : g₂ ∉ derivedInG hyp.typeI.typeF.H) :
    ψ g₁ = ψ g₂ := by
  have := hyp.finiteG
  have hg₁1 : g₁ ≠ 1 := fun h => hg₁' (h ▸ Subgroup.one_mem _)
  have hg₂1 : g₂ ≠ 1 := fun h => hg₂' (h ▸ Subgroup.one_mem _)
  set Hc := ((hyp.typeI.typeF.H).subgroupOf L) with hHc
  set x₁ : ↥Hc := ⟨⟨g₁, hyp.typeI.typeF.H_le hg₁⟩, Subgroup.mem_subgroupOf.mpr hg₁⟩ with hx₁
  set x₂ : ↥Hc := ⟨⟨g₂, hyp.typeI.typeF.H_le hg₂⟩, Subgroup.mem_subgroupOf.mpr hg₂⟩ with hx₂
  have hx₁c : x₁ ∉ commutator ↥Hc := fun hc =>
    hg₁' ((mem_commutator_subgroupOf_iff hyp.typeI.typeF.H_le x₁).mp hc)
  have hx₂c : x₂ ∉ commutator ↥Hc := fun hc =>
    hg₂' ((mem_commutator_subgroupOf_iff hyp.typeI.typeF.H_le x₂).mp hc)
  have h125 := chiRhoCF_restrict_constant_off_derived_ofData hyp data hsub h1A horth hx₁c hx₂c
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply] at h125
  rw [← heval g₁ hg₁ hg₁1, ← heval g₂ hg₂ hg₂1]
  exact h125

end OddOrder.Peterfalvi.S14


