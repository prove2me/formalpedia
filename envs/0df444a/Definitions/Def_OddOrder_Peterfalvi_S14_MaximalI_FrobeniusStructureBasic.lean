-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructureBasic
-- name    : OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructureBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:04:55.052946+00:00
-- url     : https://prove2.me/theorems/a2b13a08-5e96-4c6a-86bc-123017167e98
-- title:
--   Peterfalvi §14: Frobenius structure of type I maximals, opening layer
-- statement:
--   The opening layer of the type I Frobenius structure (Peterfalvi (12.7)): the carrier `TypeIFrobeniusData` and basic properties of the witness family $S = \{\mathrm{Ind}_H^L\theta\}$.
--
--   Main declarations: `TypeIFrobeniusData` (Carrier for Peterfalvi (12.7)); `Sset_isIrreducibleCharacter` (Witness `S = {Ind_H^L θ}` members are irreducible characters of `L`); `Sset_hasNoRealCharacters` (Witness `S = {Ind_H^L θ}` has no real characters); `Sset_pairwiseOrthogonal` (Witness `S = {Ind_H^L θ}` is pairwise orthogonal).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/FrobeniusStructureBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Carrier for Peterfalvi (12.7): a type-I maximal subgroup is Frobenius with
kernel `M_F`. -/
structure TypeIFrobeniusData (M : Subgroup G) where
  typeI : TypeIData M
  complement : Subgroup ↥M
  kernel_eq_MF : Prop
  kernel_eq_MF_holds : kernel_eq_MF
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥M (typeI.typeF.H.subgroupOf M) complement

/-- **Peterfalvi (12.1) support `A(L) = H^#` from a Frobenius witness** — the
Frobenius-parameterized core of `typeIA_eq_sharp` (below), factored out so the (12.6) case-(b)
coherence assembly can cite it
with the `hfrob` it already has (the full `typeIA_eq_sharp` derives `hfrob` from `typeI_frobenius`,
which is defined later).  Since `L` is Frobenius with kernel `H`, the centralizer of any `x ∈ H^#`
lies in `H` (`IsFrobeniusGroup.centralizer_kernel_le`), so the `A(L)`-support (`centralizerSupport`
of `H^#`) is exactly `H^#`. -/
theorem Hypothesis.typeIA_eq_sharp_of_frobenius [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  change OddOrder.GroupTheory.centralizerSupport
      (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H) L
    = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H
  ext y
  simp only [OddOrder.GroupTheory.centralizerSupport, OddOrder.GroupTheory.sharpSubgroup,
    Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyL, hy1, x, ⟨hxN, hx1⟩, hyx⟩
    have hxL : x ∈ L := hyp.typeI.typeF.H_le hxN
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      (Subgroup.mem_subgroupOf).mpr hxN
    have hx1' : (⟨x, hxL⟩ : ↥L) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hycomm : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hyx ⊢
      exact Subtype.ext hyx
    have hyN : (⟨y, hyL⟩ : ↥L) ∈ hyp.typeI.typeF.H.subgroupOf L :=
      hfrob.centralizer_kernel_le _ hxsub hx1' hycomm
    exact ⟨(Subgroup.mem_subgroupOf).mp hyN, hy1⟩
  · rintro ⟨hyN, hy1⟩
    refine ⟨hyp.typeI.typeF.H_le hyN, hy1, y, ⟨hyN, hy1⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are irreducible characters of `L`** — the crux of the (12.6)
case-(b) reduction: for a Frobenius `L` with kernel `H`, `Ind_H^L θ` (`θ ≠ 1`) is irreducible
(`isIrreducibleCharacter_induce_of_frobeniusGroup`).  This feeds the unit-norm, orthogonality, and
`ZIrr`-membership inputs of `coherent_of_constant_degree`. -/
theorem Sset_isIrreducibleCharacter [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    IsIrreducibleCharacter χ := by
  classical
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hfrob θ hθ_ne

/-- **A Frobenius `S`-member is its own constituent.**  In the Frobenius witness case `χ ∈ S` is
irreducible (`Sset_isIrreducibleCharacter`), so its `(12.2.a)` decomposition `χ = ∑_{S(χ)} φ` is a
single term: there is `φ ∈ data.constituents` with `↑φ = χ`.  Feeds the (12.5) orthogonality
`⟨ψ, coh.extension χ⟩ = 0` via `inner_psi_coherent_extension_eq_zero` (which is stated per
constituent). -/
theorem Sset_self_mem_constituents [Finite G] {L : Subgroup G} [Finite ↥L]
    [Invertible (Nat.card ↥L : ℂ)] (hyp : Hypothesis L)
    {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (data : CharacterDecompositionData hyp χ) :
    ∃ φ : IrreducibleCharacter ↥L, (φ : ClassFunction ↥L ℂ) = χ ∧ φ ∈ data.constituents := by
  classical
  have : Fintype ↥L := Fintype.ofFinite _
  have := hyp.finiteG
  have hirr : IsIrreducibleCharacter χ := Sset_isIrreducibleCharacter hyp hfrob hχ
  obtain ⟨φ₀, hφ₀⟩ := data.constituents_nonempty
  have hone : ClassFunction.inner (φ₀ : ClassFunction ↥L ℂ) χ = 1 := by
    conv_lhs => rw [data.decomp]
    rw [inner_sum_right, Finset.sum_eq_single φ₀]
    · rw [irreducibleCharacter_inner_eq_ite, if_pos rfl]
    · intro φ _ hφne; rw [irreducibleCharacter_inner_eq_ite, if_neg (Ne.symm hφne)]
    · intro h; exact absurd hφ₀ h
  refine ⟨φ₀, ?_, hφ₀⟩
  by_contra hne'
  have h0 : ClassFunction.inner (φ₀ : ClassFunction ↥L ℂ) χ = 0 := by
    have hite := irreducibleCharacter_inner_eq_ite φ₀ (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_neg (fun h => hne' (by rw [h]))] at hite
  rw [hone] at h0
  exact one_ne_zero h0

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` has no real characters** ((5.2) input for case (b)/(12.6)).  Each
member is a Frobenius-induced irreducible (`frobenius_induce_char_singleton`), non-real by the odd
order of `L` (`not_isReal_of_ne_trivial_of_odd_card'`). -/
theorem Sset_hasNoRealCharacters [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.Sset := by
  classical
  intro χ hχ
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨ξ, hξcoe, hξreal, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  rw [← hξcoe]; exact hξreal

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` is pairwise orthogonal** ((5.2) input for case (b)/(12.6)).  Each
member is an irreducible character of `L` (Frobenius induction), so two distinct members are
orthogonal by row orthogonality (`irreducibleCharacter_inner_eq_ite`). -/
theorem Sset_pairwiseOrthogonal [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal hyp.Sset := by
  classical
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  intro χ ψ hχ hψ hne
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ hψ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hψ
  obtain ⟨ξ, hξcoe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ hθ_ne
  obtain ⟨ξ', hξ'coe, _, _⟩ := frobenius_induce_char_singleton hodd hfrob θ' hθ'_ne
  rw [← hξcoe, ← hξ'coe, irreducibleCharacter_inner_eq_ite, if_neg]
  intro h
  exact hne (by rw [← hξcoe, ← hξ'coe, h])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members are unit-norm** (the `hirr` input of (5.7)/(12.6) case (b)).
Each `Ind_H^L θ` (`θ ≠ 1`) is a Frobenius-induced irreducible, so `‖Ind_H^L θ‖² = 1`
(`inner_self_induce_eq_one_of_frobeniusGroup`, the inertia-`H` norm computation). -/
theorem Sset_inner_self_eq_one [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ClassFunction.inner χ χ = 1 := by
  classical
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  exact inner_self_induce_eq_one_of_frobeniusGroup hfrob θ hθ_ne

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness `S = {Ind_H^L θ}` members share the degree `[L:H]`** (the `hconst`/`hdeg0` input of
(5.7)/(12.6) case (b)).  With `H = L_F` abelian (Def (8.3) case (b)), every `θ ∈ Irr H` is linear
(`θ(1) = 1`, `IsIrreducibleCharacter.apply_one_eq_one_of_isMulCommutative`; commutativity transfers
to `H.subgroupOf L` by the `subgroupOf_isMulCommutative` instance), so
`(Ind_H^L θ)(1) = [L:H]·θ(1) = [L:H]` (`induce_apply_one`). -/
theorem Sset_apply_one_eq_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  have : IsMulCommutative ↥hyp.typeI.typeF.H := hab
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  rw [ClassFunction.induce_apply_one, θ.isIrreducible.apply_one_eq_one_of_isMulCommutative, mul_one]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`S(H′)` is constant-degree** (the (5.7) input for `hcoh` of the (6.5.c) engine, without
assuming `H` abelian).  Every member of `S(⁅K,K⁆)` (`K = (L_F).subgroupOf L`) is `Ind_K^L θ` with
`⁅K,K⁆ ⊆ Ker θ`; then `θ` factors through the abelian `K/⁅K,K⁆`, so `θ(1) = 1`
(`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`) and `Ind θ (1) = |L:K|`.
This is Peterfalvi's `η_j(1) = |W₁|` for the `Y = S(H′)` family — the subfamily replacement for the
case-(b) `Sset_apply_one_eq_index` (which needs all of `H` abelian). -/
theorem SsubFiltration_commutator_apply_one_eq_index [Finite G] {L : Subgroup G}
    (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.SsubFiltration
      ⁅(hyp.typeI.typeF.H).subgroupOf L, (hyp.typeI.typeF.H).subgroupOf L⁆) :
    (χ : ↥L → ℂ) 1 = (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.SsubFiltration, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, _hθ_ne, hker, rfl⟩ := hχ
  have hθ1 : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) 1 = 1 := by
    have : IsMulCommutative (↥((hyp.typeI.typeF.H).subgroupOf L) ⧸
        commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥((hyp.typeI.typeF.H).subgroupOf L)))
    refine
      apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥((hyp.typeI.typeF.H).subgroupOf L)) θ ?_
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self ((hyp.typeI.typeF.H).subgroupOf L)]
    exact hker
  rw [ClassFunction.induce_apply_one, hθ1, mul_one]

open OddOrder.Peterfalvi.S09.Cert in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Witness member differences are `A(L)`-supported** (the `hsuppdiff` input of (5.7)/(12.6) case
(b), and the support that lets the Dade isometry apply — `tau_isometry_diff`).  Two members
`a, b ∈ S = {Ind_H^L θ}` both vanish off `H` (`Sset_vanishes_off_H`) and share the degree `[L:H]`
(`Sset_apply_one_eq_index`), so `a − b` vanishes off `H` and at `1`, i.e. is supported in
`A(L) = H^# = supportInSubgroup (H \ {1}) L`. -/
theorem Sset_diff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hab : IsMulCommutative ↥hyp.typeI.typeF.H)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {a b : ClassFunction ↥L ℂ} (ha : a ∈ hyp.Sset) (hb : b ∈ hyp.Sset) :
    (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (a - b) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    exact hx0 (by rw [Sset_vanishes_off_H hyp ha h, Sset_vanishes_off_H hyp hb h, sub_zero])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx0 (by
      rw [Sset_apply_one_eq_index hyp hab ha, Sset_apply_one_eq_index hyp hab hb, sub_self])
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A member's conjugate-difference `χ̄ − χ` is `A(L)`-supported** (any `χ ∈ S`, no
constant-degree needed) — the per-member support field of the (5.6) family enumeration (h56).  Off
`H` both `χ` and `χ̄` vanish (`Sset_vanishes_off_H`); at `1`, `χ̄(1) = χ(1)` because `χ(1)` is a
(real) natural degree
(`χ` irreducible), so `χ̄ − χ` is supported on `H^# = A(L)`. -/
theorem Sset_conjDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  intro x hx
  have hx0 : (χ.conj - χ) x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h]; simp
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    obtain ⟨n, -, hn1, -⟩ :=
      (Sset_isIrreducibleCharacter hyp hfrob hχ).exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast, sub_self]
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Orthonormal enumeration of a coherent `S₁ ⊆ S`** — the witness analogue of the Sibley
`exists_sMemberOrthonormalFamily`, the family-enumeration input of the (5.6) break bound (h56).
Members of `S₁` are irreducible (`Sset_isIrreducibleCharacter`), so `exists_finEnum_irreducible`
lists them as `χmem : Fin k → Irr L`; the per-member fields are the witness `Sset` facts (no-real,
`Sset_conjDiff_supported`, pairwise/self orthonormality), `hS₁conj` supplies `χ̄ ∈ S₁`. -/
theorem Sset_exists_orthonormalFamily [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    (hodd : Odd (Nat.card ↥L)) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.Sset)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → IrreducibleCharacter ↥L),
      Function.Injective χmem ∧
      Set.range (fun j => (χmem j : ClassFunction ↥L ℂ)) = S₁ ∧
      (∀ j, ¬ ClassFunction.IsReal (χmem j : ClassFunction ↥L ℂ)) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ).conj - (χmem j : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ).conj ∈ S₁) ∧
      (∀ j, ClassFunction.inner (χmem j : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ).conj = 0) ∧
      (∀ i j, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
        (χmem j : ClassFunction ↥L ℂ) = if i = j then (1 : ℂ) else 0) := by
  have hS₁irr : ∀ φ ∈ S₁, IsIrreducibleCharacter φ :=
    fun φ hφ => Sset_isIrreducibleCharacter hyp hfrob (hS₁sub hφ)
  obtain ⟨k, χmem, hχinj, hrange⟩ :=
    OddOrder.Peterfalvi.S08.exists_finEnum_irreducible hS₁fin hS₁irr
  have hmemS1 : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ S₁ := by
    intro j; rw [← hrange]; exact Set.mem_range_self j
  refine ⟨k, χmem, hχinj, hrange, ?_, ?_, hmemS1, ?_, ?_, ?_⟩
  · intro j
    exact Sset_hasNoRealCharacters hyp hodd hfrob (hS₁sub (hmemS1 j))
  · intro j
    exact Sset_conjDiff_supported hyp hfrob hAH (hS₁sub (hmemS1 j))
  · intro j
    exact hS₁conj (hmemS1 j)
  · intro j
    have hχS := hS₁sub (hmemS1 j)
    have hne : (χmem j : ClassFunction ↥L ℂ) ≠ (χmem j : ClassFunction ↥L ℂ).conj :=
      fun h => (Sset_hasNoRealCharacters hyp hodd hfrob hχS) h.symm
    exact Sset_pairwiseOrthogonal hyp hodd hfrob hχS (Sset_closedUnderConjugate hyp hχS) hne
  · intro i j
    rw [OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite (χmem i) (χmem j)]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg (fun he => h (hχinj he)), if_neg h]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A member's degree is `d·|L:K|`** (`d = θ(1)` the source degree) — the integer degree-ratio
input of the (5.6) degree data (h56).  `χ = Ind_K^L θ` has `χ(1) = |L:K|·θ(1)` (`induce_apply_one`),
`θ(1)` a positive natural (`θ` irreducible). -/
theorem Sset_charValue_one_eq_mul_index [Finite G] {L : Subgroup G} (hyp : Hypothesis L)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) :
    ∃ d : ℕ, 0 < d ∧
      (χ : ↥L → ℂ) 1 = (d : ℂ) * (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) := by
  classical
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hχ
  obtain ⟨θ, -, rfl⟩ := hχ
  obtain ⟨d, hd0, hd1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  refine ⟨d, hd0, ?_⟩
  rw [ClassFunction.induce_apply_one, hd1]
  ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S09.Cert in
/-- **A scaled difference `χ − m·χ′` is `A(L)`-supported** when `χ(1) = m·χ′(1)` (any `χ, χ′ ∈ S`) —
the per-member scaled-difference support of the (5.6) degree data (h56).  Off `H` both vanish
(`Sset_vanishes_off_H`); at `1` the degree relation makes it vanish; so it is supported on
`H^# = A(L)`. -/
theorem Sset_scaledDiff_supported [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (_hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset) {m : ℕ}
    (hdeg : (χ : ↥L → ℂ) 1 = (m : ℂ) * (χ' : ↥L → ℂ) 1) :
    (χ - m • χ').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  rw [show (m • χ' : ClassFunction ↥L ℂ) = (m : ℂ) • χ' from
    (Nat.cast_smul_eq_nsmul ℂ m χ').symm]
  intro x hx
  have hx0 : (χ - (m : ℂ) • χ') x ≠ 0 := ClassFunction.mem_support.mp hx
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply] at hx0
  have hxH : (x : G) ∈ hyp.H := by
    by_contra h
    apply hx0
    rw [Sset_vanishes_off_H hyp hχ h, Sset_vanishes_off_H hyp hχ' h]; ring
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hx0
    rw [hdeg]; ring
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff hyp.typeI.typeF.H hAH x).mpr
    ⟨Subgroup.mem_subgroupOf.mpr hxH, hx1⟩

/-- **Degree data for an enumerated `S`-family** — the witness analogue of the Sibley
`exists_sMemberDegreeData`, the integer-degree-ratio input of the (5.6) break bound (h56).  Against
a minimal-degree anchor `χmem i₁` of degree `|L:K|`, each member has an integer ratio
`deg j = χmem j(1)/|L:K|` (`Sset_charValue_one_eq_mul_index`), `deg i₁ = 1`, and the scaled
difference `χmem j − deg j·χmem i₁` is `A(L)`-supported (`Sset_scaledDiff_supported`). -/
theorem Sset_exists_degreeData [Finite G] {L : Subgroup G} (hyp : Hypothesis L) {C : Subgroup ↥L}
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L ((hyp.typeI.typeF.H).subgroupOf L) C)
    (hAH : hyp.ambientA = ((hyp.typeI.typeF.H) : Set G) \ {1})
    {k : ℕ} {χmem : Fin k → IrreducibleCharacter ↥L} {i₁ : Fin k}
    (hmemS : ∀ j, (χmem j : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hanchordeg : (χmem i₁ : ClassFunction ↥L ℂ) 1 =
      (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ)) :
    ∃ deg : Fin k → ℕ, deg i₁ = 1 ∧ (∀ j, 0 < deg j) ∧
      (∀ j, (χmem j : ClassFunction ↥L ℂ) 1 = (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1) ∧
      (∀ j, ((χmem j : ClassFunction ↥L ℂ) - deg j • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) := by
  choose deg hdeg_pos hdeg_eq using fun j => Sset_charValue_one_eq_mul_index hyp (hmemS j)
  have hdeg_eq' : ∀ j, (χmem j : ClassFunction ↥L ℂ) 1 =
      (deg j : ℂ) * (χmem i₁ : ClassFunction ↥L ℂ) 1 := fun j => by
    rw [hdeg_eq j, hanchordeg]
  refine ⟨deg, ?_, hdeg_pos, hdeg_eq', fun j =>
    Sset_scaledDiff_supported hyp hfrob hAH (hmemS j) (hmemS i₁) (hdeg_eq' j)⟩
  have h := hdeg_eq i₁
  rw [hanchordeg] at h
  have hidx_ne : (((hyp.typeI.typeF.H).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdeg1 : (deg i₁ : ℂ) = 1 := mul_right_cancel₀ hidx_ne (by rw [one_mul]; exact h.symm)
  exact_mod_cast hdeg1

end OddOrder.Peterfalvi.S14


