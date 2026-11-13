-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoGeneral
-- name    : OddOrder_Peterfalvi_S08_SixTwoGeneral
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:23:50.145454+00:00
-- url     : https://prove2.me/theorems/bf77a61f-4d39-4f2a-886e-2899aec05565
-- title:
--   Peterfalvi (6.2), general kernel: the induced family $S(X)$
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.1)/(6.2). This file builds the general-kernel (6.1) induced family for the general (6.2) index bound $|K:A|-1\le 2\psi(1)$, the break-member oracle of the standalone (6.3) statement; the Sibley-case analogue was built earlier.
--
--   Results include `inducedKernelFamily_mem_ZIrr` (members are virtual characters of $L$), `inducedKernelFamily_degree_ratio` (member degree ratio against the index anchor), `sum_re_div_normSq_inducedKernelFamily_eq` (the (6.2) degree-square sum, real form), `inducedKernelFamily_degreeSqNormReBound_of_break_k_general` (the norm-weighted degree-square bound) and `inducedKernelFamily_memberDatum_of_irreducible` (the per-member (5.2.d) datum).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SixTwoGeneral.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SixTwoGeneral.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S08_Theorem62_63_Standalone
import Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoinWeighted
import Definitions.Def_OddOrder_Peterfalvi_S08_InducedKernelFamily

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

variable {L : Subgroup G} [Fintype ↥L]

section InducedKernelFamily

variable (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]

variable {K}

/-- `S(X)` is finite (image of the finite irreducible-character set of `↥K`). -/
theorem inducedKernelFamily_finite (X : Subgroup ↥L) :
    (inducedKernelFamily K X).Finite := by
  classical
  have : Fintype ↥K := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter ↥K) := finite_irreducibleCharacter (G := ↥K)
  refine (Set.finite_range
    (fun θ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (θ : ClassFunction ↥K ℂ))).subset ?_
  rintro φ ⟨θ, -, -, rfl⟩
  exact ⟨θ, rfl⟩

omit [Fintype ↥L] [Invertible (Nat.card ↥K : ℂ)] in
/-- A nontrivial irreducible character of `↥K` stays nontrivial after complex conjugation
(the trivial character is real, and conjugation is involutive). -/
theorem irreducibleCharacter_conj_ne_trivial_of_ne_trivial [Finite ↥K]
    {θ : IrreducibleCharacter ↥K}
    (hθne : θ ≠ trivialIrreducibleCharacter ↥K) :
    (⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩ : IrreducibleCharacter ↥K) ≠
      trivialIrreducibleCharacter ↥K := by
  intro hθc
  apply hθne
  apply IrreducibleCharacter.ext
  have hval : (θ : ClassFunction ↥K ℂ).conj =
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) :=
    congrArg (fun η : IrreducibleCharacter ↥K => (η : ClassFunction ↥K ℂ)) hθc
  calc (θ : ClassFunction ↥K ℂ)
      = ((θ : ClassFunction ↥K ℂ).conj).conj := by rw [ClassFunction.conj_conj]
    _ = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ).conj := by rw [hval]
    _ = (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by ext x; simp

/-- `S(X)` is closed under complex conjugation: conjugating the source
(`ClassFunction.induce_conj`) preserves nontriviality and the kernel condition
(`characterKernel_conj`). -/
theorem inducedKernelFamily_closedUnderConjugate (X : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (inducedKernelFamily K X) := by
  intro φ hφ
  obtain ⟨θ, hθne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥K := ⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, irreducibleCharacter_conj_ne_trivial_of_ne_trivial hθne, ?_, ?_⟩
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj K (θ : ClassFunction ↥K ℂ)

/-- **Member degree formula**: an `S(X)`-member `Ind_K^L θ` has degree `|L:K| · θ(1)`. -/
theorem inducedKernelFamily_apply_one {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) :
    ∃ θ : IrreducibleCharacter ↥K,
      θ ≠ trivialIrreducibleCharacter ↥K ∧
      φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∧
      φ 1 = (K.index : ℂ) * (θ : ClassFunction ↥K ℂ) 1 := by
  obtain ⟨θ, hθne, -, hφeq⟩ := hφ
  exact ⟨θ, hθne, hφeq, by rw [hφeq, ClassFunction.induce_apply_one]⟩

/-- **The degree-`|L:K|` anchor member of `S(X)`** (the (6.2) anchor source, mmd 04.8 L14; Coq
`exists_linInd`): when `K/X` has proper commutator subgroup, a nontrivial linear character of
`K/X` inflates to a degree-one `θ ∈ Irr K` trivial on `X`, whose induction is an `S(X)`-member
of degree `|L:K|`. -/
theorem exists_inducedKernelFamily_member_degree_index {X : Subgroup ↥L}
    [(X.subgroupOf K).Normal]
    (hXcomm : commutator (↥K ⧸ X.subgroupOf K) ≠ ⊤) :
    ∃ φ ∈ inducedKernelFamily K X, φ (1 : ↥L) = (K.index : ℂ) := by
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨θ, hθne, hθker, hθdeg⟩ :=
    exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top
      (X.subgroupOf K) hXcomm
  exact ⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ),
    ⟨θ, hθne, hθker, rfl⟩,
    by rw [ClassFunction.induce_apply_one, hθdeg, mul_one]⟩

end InducedKernelFamily

section FamilyStructure

variable [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **Distinct members of `S(X)` are orthogonal** (members from distinct source orbits;
`induce_eq_induce_iff_conj` + `inner_induce_eq_zero_of_not_conj`).  No irreducibility of the
members: this is the pairwise orthogonality of the possibly-reducible general family. -/
theorem inducedKernelFamily_pairwise_orthogonal {X Y : Subgroup ↥L}
    {φ φ' : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) (hφ' : φ' ∈ inducedKernelFamily K Y)
    (hne : φ ≠ φ') :
    ClassFunction.inner φ φ' = 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨θ', -, -, rfl⟩ := hφ'
  have : Fintype ↥K := Fintype.ofFinite _
  refine inner_induce_eq_zero_of_not_conj θ θ' (fun g hg => hne ?_)
  exact (induce_eq_induce_iff_conj θ θ').mpr ⟨g, hg⟩

/-- **Members of `S(X)` have real, positive squared norm** — `⟨φ, φ⟩ = ‖φ‖²·1` with
`0 < ‖φ‖².re` (`|K| · ⟨Ind θ, Ind θ⟩ = |I_L(θ)| > 0`,
`card_mul_inner_self_induce_eq_card_inertia`). -/
theorem inducedKernelFamily_inner_self_real_pos {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) ∧
      0 < (ClassFunction.inner φ φ).re := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  have : Fintype ↥K := Fintype.ofFinite _
  constructor
  · rw [inner_self_eq_realCast (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)),
      Complex.ofReal_re]
  · have hcard := card_mul_inner_self_induce_eq_card_inertia (G := ↥L) (H := K) (θ := θ)
    set φ := ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
    -- take real parts: `|K| · ⟨φ,φ⟩.re = |I_L(θ)|`
    have hre : (Nat.card ↥K : ℝ) * (ClassFunction.inner φ φ).re
        = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℝ) := by
      have := congrArg Complex.re hcard
      simpa [Complex.mul_re] using this
    have hKpos : (0 : ℝ) < (Nat.card ↥K : ℝ) := by exact_mod_cast Nat.card_pos
    have hIpos : (0 : ℝ)
        < (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥K ℂ)) : ℝ) := by
      exact_mod_cast Nat.card_pos
    nlinarith [hre]

/-- **`S(X)` has no real members** for `L` of odd order (Peterfalvi (1.1) extended to the
possibly-reducible family): `Ind_K^L θ` real would force `θ̄ = θ^g` for some `g ∈ L`
(`induce_conj` + `induce_eq_induce_iff_conj`), impossible in odd order
(`conjBy_ne_conj_of_odd` — `θ = θ^{g²}` and `⟨g⟩ = ⟨g²⟩` give `θ̄ = θ`, but a nontrivial
irreducible of an odd-order group is non-real). -/
theorem inducedKernelFamily_hasNoRealCharacters (hodd : Odd (Nat.card ↥L)) (X : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (inducedKernelFamily K X) := by
  rintro φ ⟨θ, hθne, -, rfl⟩ hreal
  have : Fintype ↥K := Fintype.ofFinite _
  -- realness transfers to the sources: `Ind θ = (Ind θ)̄ = Ind θ̄`.
  let θc : IrreducibleCharacter ↥K := ⟨(θ : ClassFunction ↥K ℂ).conj, θ.isIrreducible.conj⟩
  have hind : ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θc : ClassFunction ↥K ℂ) := by
    have h1 : (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)).conj
        = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) := hreal
    calc ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        = (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)).conj := h1.symm
      _ = ClassFunction.induce K (θc : ClassFunction ↥K ℂ) :=
          ClassFunction.induce_conj K (θ : ClassFunction ↥K ℂ)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ θc).mp hind
  have hθneCF : (θ : ClassFunction ↥K ℂ) ≠ trivialClassFunction ↥K :=
    fun h => hθne (Subtype.ext h)
  refine conjBy_ne_conj_of_odd hodd θ.isIrreducible hθneCF g ?_
  have := congrArg (fun η : IrreducibleCharacter ↥K => (η : ClassFunction ↥K ℂ)) hg
  simpa [IrreducibleCharacter.coe_conjBy, θc] using this

end FamilyStructure

section SupportLemmas

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [K.Normal] in
/-- Every `S(X)`-member is a virtual character of `L` (`Ind_K^L θ ∈ ℤ[Irr L]`). -/
theorem inducedKernelFamily_mem_ZIrr [Invertible (Nat.card ↥L : ℂ)] {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    φ ∈ ZIrr ↥L := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  have : Fintype ↥K := Fintype.ofFinite _
  exact ClassFunction.induce_mem_ZIrr K θ.mem_ZIrr

/-- **Scaled member differences are `K^#`-supported.**  For members `φ, φ' ∈ S(X)`/`S(Y)` with
matching degrees `φ(1) = d·φ'(1)`, the difference `φ − d·φ'` vanishes off `K` (induced characters
of the normal `K` vanish there, `induce_apply_eq_zero_of_not_mem_normal`) and at `1` (degree
match), so its support lies in any set containing `K ∖ {1}`.  This discharges the (5.6) engine's
support conditions (`hmemdegdiffsupp`/`hdiffasuppχ`) once the §11 consumer knows
`K^# ⊆ A₀` for its Dade support set `A₀`. -/
theorem inducedKernelFamily_scaledDiff_support {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {X Y : Subgroup ↥L} {φ φ' : ClassFunction ↥L ℂ}
    (hφ : φ ∈ inducedKernelFamily K X) (hφ' : φ' ∈ inducedKernelFamily K Y)
    {d : ℕ} (hdeg : φ 1 = (d : ℂ) * φ' 1) :
    (φ - d • φ').support ⊆ A0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨θ', -, -, rfl⟩ := hφ'
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hnsmul : ∀ (ψ : ClassFunction ↥L ℂ) (y : ↥L), (d • ψ) y = (d : ℂ) * ψ y := by
    intro ψ y
    rw [← Nat.cast_smul_eq_nsmul ℂ d ψ, ClassFunction.smul_apply]
  have hval : ∀ y : ↥L,
      (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)
        - d • ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) y
      = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) y
        - (d : ℂ) * ClassFunction.induce K (θ' : ClassFunction ↥K ℂ) y := by
    intro y
    rw [ClassFunction.sub_apply, hnsmul]
  refine hKsupp x ?_ ?_
  · -- off `K` both induced characters vanish
    by_contra hxK
    refine hx ?_
    rw [hval, ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hxK,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hxK, mul_zero, sub_zero]
  · -- at `1` the degrees cancel
    intro hx1
    refine hx ?_
    rw [hx1, hval, hdeg, sub_self]

/-- **Conjugate member differences are `K^#`-supported**: `(φ̄ − φ).support ⊆ A₀` for a member
`φ ∈ S(X)` (the (5.6) engine's `hdiffsuppχ`/`hmemdiffsupp`).  Special case of the scaled
difference at `d = 1`: `φ̄` is again a member (`inducedKernelFamily_closedUnderConjugate`) of the
same (real, integral) degree `φ̄(1) = star φ(1) = φ(1)`. -/
theorem inducedKernelFamily_conjDiff_support {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    (φ.conj - φ).support ⊆ A0 := by
  have hφc := inducedKernelFamily_closedUnderConjugate X hφ
  have hdeg : φ.conj 1 = ((1 : ℕ) : ℂ) * φ 1 := by
    obtain ⟨θ, -, -, rfl⟩ := hφ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    rw [Nat.cast_one, one_mul, ClassFunction.conj_apply, ClassFunction.induce_apply_one, hd]
    rw [show ((K.index : ℂ) * (d : ℂ)) = ((K.index * d : ℕ) : ℂ) by push_cast; ring]
    exact star_natCast _
  have h := inducedKernelFamily_scaledDiff_support hKsupp hφc hφ (d := 1) hdeg
  simpa using h

end SupportLemmas

section BreakFields

variable [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **Member degree ratio against the index anchor.**  Every `S(X)`-member has degree an
integral multiple of `|L:K|`: `φ(1) = d · (K.index : ℂ)` with `d = θ(1) ∈ ℕ` positive.  This is
the divisibility `|L:K| ∣ ψ(1)` of the (6.2) proof (Coq: `dvdC_mulr`/`Cnat_irr1`), producing the
(5.6) engine's `deg` ratios once the anchor `χ₁(1) = |L:K|` is fixed. -/
theorem inducedKernelFamily_degree_ratio {X : Subgroup ↥L}
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ inducedKernelFamily K X) :
    ∃ d : ℕ, 0 < d ∧ φ 1 = (d : ℂ) * (K.index : ℂ) := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  exact ⟨d, hdpos, by rw [ClassFunction.induce_apply_one, hd]; ring⟩

/-- **The general break-character fields** — the break-side inputs of the norm-weighted (5.6)
engine, packaged for a break `ψ ∈ S(B)` whose conjugate pair avoids `S₁ ⊆ S = S(⊥)`.

General-family analogue of `caseB_breakChar_fields`/`caseB_breakChar_fields_columnBreak`
(`S08_CaseBEnumeration`): non-reality (odd order), nonzero self-norms (norm positivity), vanishing
cross-norms and orthogonality to `S₁` (distinct family members are orthogonal), and the
`A₀`-supported conjugate difference. -/
theorem inducedKernelFamily_breakChar_fields
    (hodd : Odd (Nat.card ↥L)) {A0 : Set ↥L}
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A0)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ ≠ 0 ∧ ClassFunction.inner ψ.conj ψ.conj ≠ 0 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ A0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  have hψc := inducedKernelFamily_closedUnderConjugate B hψB
  have hreal : ¬ ClassFunction.IsReal ψ := inducedKernelFamily_hasNoRealCharacters hodd B hψB
  have hψconj_ne : ψ.conj ≠ ψ := fun h => hreal h
  have hnormψ := inducedKernelFamily_inner_self_real_pos hψB
  have hnormψc := inducedKernelFamily_inner_self_real_pos hψc
  refine ⟨hreal, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnormψ.1]
    exact_mod_cast hnormψ.2.ne'
  · rw [hnormψc.1]
    exact_mod_cast hnormψc.2.ne'
  · exact inducedKernelFamily_pairwise_orthogonal hψc hψB hψconj_ne
  · exact inducedKernelFamily_pairwise_orthogonal hψB hψc (fun h => hψconj_ne h.symm)
  · exact inducedKernelFamily_conjDiff_support hKsupp hψB
  · intro χ hχ
    exact inducedKernelFamily_pairwise_orthogonal
      (inducedKernelFamily_subset_bot B hψB) (hS₁sub hχ)
      (fun h => hψnotS1 (h ▸ hχ))
  · intro χ hχ
    exact inducedKernelFamily_pairwise_orthogonal
      (inducedKernelFamily_subset_bot B hψc) (hS₁sub hχ)
      (fun h => hψcnotS1 (h ▸ hχ))

end BreakFields

section DegreeSum

variable [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

omit [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
open scoped Classical in
/-- The kernel-filter image Finset of `sum_div_normSq_induce_kernelFilter_eq` enumerates exactly
the family `S(X) = inducedKernelFamily K X` (as a set). -/
theorem coe_kernelFilter_image_eq_inducedKernelFamily (X : Subgroup ↥L) :
    ↑((Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
          (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction))
      = inducedKernelFamily K X := by
  ext φ
  rw [Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hθ
    exact ⟨θ, hθ.2.2, hθ.2.1, rfl⟩
  · rintro ⟨θ, hθne, hker, rfl⟩
    exact ⟨θ, by rw [Finset.mem_coe, Finset.mem_filter]; exact ⟨Finset.mem_univ θ, hker, hθne⟩,
      rfl⟩

open scoped Classical in
/-- **(6.2) degree-square sum over the general filtration `S(X)`, real form.**

The norm-weighted degree-square sum over `S(X) = {Ind_K^L θ | X ⊆ Ker θ, θ ≠ 1}` is
`|L:K|·(|K:X| − 1)` (Peterfalvi (6.2) proof, mmd 04.8 L13-17; Coq `sum_seqIndD_square`).
General-kernel form of `sum_re_div_normSq_SsubFiltration_eq` (`S08_Theorem63`, `K = H` Sibley):
the complex orbit-count identity `sum_div_normSq_induce_kernelFilter_eq` followed by the
per-summand real conversion (`χ(1)` a real degree, `⟨χ,χ⟩` real). -/
theorem sum_re_div_normSq_inducedKernelFamily_eq (X : Subgroup ↥L) [X.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
            (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                (θ : ClassFunction ↥K ℂ) ∧
              θ ≠ trivialIrreducibleCharacter ↥K)).image
          (fun θ => ClassFunction.induce K θ.toClassFunction),
        ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      = (K.index : ℝ) * ((Nat.card (↥K ⧸ X.subgroupOf K) : ℝ) - 1) := by
  -- the complex weighted `S(X)` identity.
  have hcomplex := @sum_div_normSq_induce_kernelFilter_eq ↥L _ _ _ K _ _ X _
  -- per-summand real conversion `χ(1)²/⟨χ,χ⟩ = (χ(1).re²/⟨χ,χ⟩.re : ℂ)`.
  have hconv : ∀ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
          (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥K)).image
        (fun θ => ClassFunction.induce K θ.toClassFunction),
      χ 1 ^ 2 / ClassFunction.inner χ χ
        = (((χ 1).re ^ 2 / (ClassFunction.inner χ χ).re : ℝ) : ℂ) := by
    intro χ hχ
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hχ1 : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : ↥L)
        = ((K.index * d : ℕ) : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd]; push_cast; ring
    have hr : (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) (1 : ↥L)).re
        = ((K.index * d : ℕ) : ℝ) := by
      rw [hχ1, Complex.natCast_re]
    rw [hr, hχ1, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    congr 1
    rw [inner_self_eq_realCast (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)),
      Complex.ofReal_re]
  -- combine: cast the real sum to `ℂ`, rewrite each summand, identify with `hcomplex`.
  have key : (((∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
              (↑(X.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
                  (θ : ClassFunction ↥K ℂ) ∧
                θ ≠ trivialIrreducibleCharacter ↥K)).image
            (fun θ => ClassFunction.induce K θ.toClassFunction),
          ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re : ℝ)) : ℂ)
      = (((K.index : ℝ) * ((Nat.card (↥K ⧸ X.subgroupOf K) : ℝ) - 1)) : ℝ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun χ hχ => (hconv χ hχ).symm), hcomplex]
    push_cast; ring
  exact Complex.ofReal_inj.mp key

end DegreeSum

section MemberFamilyBound

variable [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

open scoped Classical in
/-- **The general-kernel norm-weighted member-family degree-square bound, abstract `τ`.**

The `τ`-general form of `inducedKernelFamily_degreeSqNormReBound_of_break_k` (issue 0154): instead
of the Feit–Thompson Dade map on `supportInSubgroup A L`, it takes an arbitrary integral map `τ`
together with the two clauses of Peterfalvi **Hypothesis (5.2.b)** on the `A₀`-supported sublattice
of `ℤ[𝒮]` (`𝒮 = inducedKernelFamily K ⊥`):

* `hisom` — `τ` is an isometry there (the book's "linear isometry"), and
* `htauZ` — `τ` lands in `ℤ[Irr G]` there (the book's codomain `ℤ[Irr G, G^#]`).

Those are exactly the two places the Dade map was used; everything else is the family-structure
layer of this file (enumeration, Gram matrix, degree ratios, supports, generation, break fields)
plus the `τ`-general weighted (5.6) engine
`S07.coherentDegreeSqNormBound_of_not_coherentW_k_general`. -/
theorem inducedKernelFamily_degreeSqNormReBound_of_break_k_general
    {A₀ : Set ↥L}
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]
    (hisom : ∀ ⦃φ ζ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ζ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (htauZ : ∀ ⦃φ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      τ φ ∈ ZIrr G)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A₀)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (K.index : ℂ))
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ ψ (a • χ₁))
    (hDatau1 : Da.tau1 = τ)
    (datum : ∀ χ ∈ S₁,
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ χ 0 //
        D.imageFamily.Orthogonal Da.imageFamily ∧
        D.tau1 χ = hS₁coh.extension χ })
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A₀)) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, 0 < mc j) ∧
      (∀ j, ClassFunction.inner (χmem j) (χmem j) = ((mc j : ℝ) : ℂ)) ∧
      ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  classical
  -- the `T`-indexed shape of (5.2.b) that the general engine consumes
  have hisomT : ∀ (T : Set (ClassFunction ↥L ℂ)),
      (∀ s ∈ T, s ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (inducedKernelFamily K ⊥) A₀) →
      ∀ φ ζ : ClassFunction ↥L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ :=
    fun _T hT _φ _ζ hφ hζ =>
      hisom (OddOrder.Peterfalvi.S07.zSpan_subset_zSupportedSpan hT hφ)
        (OddOrder.Peterfalvi.S07.zSpan_subset_zSupportedSpan hT hζ)
  -- (1) enumeration of `S₁` and its membership in the full family
  obtain ⟨k, χmem, hinj, hrange⟩ := exists_finEnum_general hS₁fin
  have hmemS1set : ∀ j, χmem j ∈ S₁ := fun j => hrange ▸ Set.mem_range_self j
  have hmemfam : ∀ j, χmem j ∈ inducedKernelFamily K ⊥ := fun j => hS₁sub (hmemS1set j)
  -- (2) norms `mc` and the weighted Gram matrix
  set mc : Fin k → ℝ := fun j => (ClassFunction.inner (χmem j) (χmem j)).re with hmc
  have hmcpos : ∀ j, 0 < mc j := fun j =>
    (inducedKernelFamily_inner_self_real_pos (hmemfam j)).2
  have hmcnorm : ∀ j, ClassFunction.inner (χmem j) (χmem j) = ((mc j : ℝ) : ℂ) := fun j =>
    (inducedKernelFamily_inner_self_real_pos (hmemfam j)).1
  have hmemortho : ∀ i j, ClassFunction.inner (χmem i) (χmem j)
      = @ite ℂ (i = j) (Classical.propDecidable (i = j)) ((mc i : ℝ) : ℂ) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact hmcnorm i
    · rw [if_neg hij]
      exact inducedKernelFamily_pairwise_orthogonal (hmemfam i) (hmemfam j)
        (fun h => hij (hinj h))
  -- (3) the anchor's index `i₁` in the enumeration (and eliminate `χ₁` in its favour)
  have hχ₁mem : χ₁ ∈ Set.range χmem := hrange ▸ hχ₁S₁
  obtain ⟨i₁, hi₁eq⟩ := hχ₁mem
  subst hi₁eq
  -- (4) degree ratios `deg` against the index anchor
  choose deg hdegpos hdegeq using fun j => inducedKernelFamily_degree_ratio (hmemfam j)
  have hKidx_ne : (K.index : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hdeg_anchor : ∀ j, χmem j 1 = (deg j : ℂ) * χmem i₁ 1 := fun j => by
    rw [hdegeq j, hχ₁deg]
  have ha1 : deg i₁ = 1 := by
    have h : (deg i₁ : ℂ) * (K.index : ℂ) = 1 * (K.index : ℂ) := by
      rw [one_mul, ← hdegeq i₁, hχ₁deg]
    have h1 := mul_right_cancel₀ hKidx_ne h
    exact_mod_cast h1
  -- (5) break-character fields
  obtain ⟨hreal, hψψne, hψbψbne, hψbψ, hψψb, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    inducedKernelFamily_breakChar_fields hodd hKsupp hS₁sub hψB hψnotS1 hψcnotS1
  -- (6) support conditions for the scaled differences
  have hmemdegdiffsupp : ∀ (i : Fin k), i ∈ (Finset.univ : Finset (Fin k)) →
      ((χmem i - deg i • χmem i₁).support ⊆ A₀) := by
    intro i _
    exact inducedKernelFamily_scaledDiff_support hKsupp (hmemfam i) (hmemfam i₁)
      (d := deg i) (hdeg_anchor i)
  have hdiffasuppψ : (ψ - a • χmem i₁).support ⊆ A₀ :=
    inducedKernelFamily_scaledDiff_support hKsupp hψB (hmemfam i₁) (d := a) hψdeg
  -- (7) the supported-lattice memberships that (5.2.b) is stated on
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  have hadiffmem : ψ - a • χmem i₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) A₀ :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam)
        (nsmul_mem (Submodule.subset_span (hmemfam i₁)) a), hdiffasuppψ⟩
  have hdiffmem : ψ - ψ.conj ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
      (inducedKernelFamily K ⊥) A₀ :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hψfam) (Submodule.subset_span hψcfam), by
        rw [show ψ - ψ.conj = -(ψ.conj - ψ) from by abel, ClassFunction.support_neg]
        exact hdiffsuppψ⟩
  have hmemdegdiffmem : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      χmem i - deg i • χmem i₁ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁ A₀ :=
    fun i hi => OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span (hmemS1set i))
        (nsmul_mem (Submodule.subset_span (hmemS1set i₁)) (deg i)), hmemdegdiffsupp i hi⟩
  -- (8) `(5.2.b)` codomain: the break difference has an integral image
  have htau1ψ : τ (ψ - a • χmem i₁) ∈ ZIrr G := htauZ hadiffmem
  -- (9) generation: anchor generation of `ℤ[S₁]` and the adjoined-pair supported span
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
    hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hψ1cast : ψ 1 = ((a * K.index : ℕ) : ℂ) := by
    rw [hψdeg, hχ₁deg]; push_cast; ring
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply, hψ1cast]
    exact star_natCast _
  have hχ₁ne : χmem i₁ 1 ≠ 0 := by
    rw [hχ₁deg]; exact hKidx_ne
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := χmem i₁) (a := a)
    hSgen hψdeg hbar1 hχ₁ne h1A
  -- (10) feed the `τ`-general norm-weighted reducible-break engine
  have hbound := OddOrder.Peterfalvi.S07.coherentDegreeSqNormBound_of_not_coherentW_k_general
    (Samb := inducedKernelFamily K ⊥) hS₁coh hS₁sub hisomT
    ψ hψψne hψbψbne hψψb hψbψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    hmemdegdiffmem (fun j _ => hmemS1set j) mc (fun j _ => hmcpos j)
    (fun i _ j _ => hmemortho i j)
    (fun χ hχ => (datum (χmem χ) (hmemS1set χ)).1)
    Da hDatau1
    (fun i _ => (datum (χmem i) (hmemS1set i)).2.1)
    (fun i _ => (datum (χmem i) (hmemS1set i)).2.2)
    hdiffmem hadiffmem htau1ψ ha1 hSgen hgen hnc
  -- (11) convert the ratio bound to the real degree-square form
  refine ⟨k, χmem, mc, hinj, hrange, hmcpos, hmcnorm, ?_⟩
  have hdegre : ∀ j, (χmem j 1).re = (deg j : ℝ) * (χmem i₁ 1).re := by
    intro j
    rw [hdeg_anchor j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (ψ 1).re = (a : ℝ) * (χmem i₁ 1).re := by
    rw [hψdeg, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  calc ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j
      = ∑ j : Fin k, ((deg j : ℝ) * (χmem i₁ 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (χmem i₁ 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 / mc j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (χmem i₁ 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * ((a : ℝ) * (χmem i₁ 1).re) * (χmem i₁ 1).re := by ring
    _ = 2 * (ψ 1).re * (χmem i₁ 1).re := by rw [hψre]

/-- **The (6.2) `S(A)`-sum bound at a break, abstract `τ`.**

The `τ`-general form of `inducedKernelFamily_SA_sum_le_two_psi_k` (issue 0154): the enumerated
family bound of `inducedKernelFamily_degreeSqNormReBound_of_break_k_general` dominates the
`S(A')`-sum, and the (B2) identity `∑_{χ ∈ S(A')} χ(1)²/‖χ‖² = |L:K|(|K:A'| − 1)` converts it into
`|L:K|·(|K:A'| − 1) ≤ 2·ψ(1)·χ₁(1)`.  Everything after the family bound is `τ`-free arithmetic. -/
theorem inducedKernelFamily_SA_sum_le_two_psi_k_general
    {A₀ : Set ↥L}
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]
    (hisom : ∀ ⦃φ ζ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ζ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (htauZ : ∀ ⦃φ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      τ φ ∈ ZIrr G)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A₀)
    {A' : Subgroup ↥L} [A'.Normal] (hSAsub : inducedKernelFamily K A' ⊆ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    (hχ₁deg : χ₁ 1 = (K.index : ℂ))
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ ψ (a • χ₁))
    (hDatau1 : Da.tau1 = τ)
    (datum : ∀ χ ∈ S₁,
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ χ 0 //
        D.imageFamily.Orthogonal Da.imageFamily ∧
        D.tau1 χ = hS₁coh.extension χ })
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A₀)) :
    (K.index : ℝ) * ((Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1)
      ≤ 2 * (ψ 1).re * (χ₁ 1).re := by
  classical
  obtain ⟨k, χmem, mc, hinj, hrange, hmcpos, hmcnorm, hfambound⟩ :=
    inducedKernelFamily_degreeSqNormReBound_of_break_k_general τ hisom htauZ hodd hKsupp h1A
      hS₁sub hS₁fin hS₁coh hχ₁S₁ hχ₁deg hψB hψnotS1 hψcnotS1 hψdeg Da hDatau1 datum hnc
  have hSAsum := sum_re_div_normSq_inducedKernelFamily_eq (K := K) (X := A')
  set SAfilt := (Finset.univ.filter (fun θ : IrreducibleCharacter ↥K =>
          (↑(A'.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥K ℂ) ∧
            θ ≠ trivialIrreducibleCharacter ↥K)).image
          (fun θ => ClassFunction.induce K θ.toClassFunction) with hSAdef
  have hsub : SAfilt ⊆ (Set.range χmem).toFinset := by
    intro χ hχ
    rw [Set.mem_toFinset, hrange]
    rw [hSAdef] at hχ
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨-, hker, hne⟩ := Finset.mem_filter.mp hθ
    exact hSAsub ⟨θ, hne, hker, rfl⟩
  rw [← hSAsum]
  calc ∑ χ ∈ SAfilt, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re
      ≤ ∑ χ ∈ (Set.range χmem).toFinset, ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun χ _ _ => div_nonneg (sq_nonneg _) (inner_self_re_nonneg χ))
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re :=
        sum_toFinset_range_eq hinj (fun χ => ((χ 1).re) ^ 2 / (ClassFunction.inner χ χ).re)
    _ = ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hmcnorm j, Complex.ofReal_re]
    _ ≤ 2 * (ψ 1).re * (χ₁ 1).re := hfambound

end MemberFamilyBound

/-- **First obstruction to coherence, union form** — the (6.2) break pair for **incomparable**
`Sa`, `Sb` (no `Sa ⊆ Sb` demanded).

Peterfalvi (6.2) makes no inclusion assumption between the coherent `S(A)` and the incoherent
`S(B)` — the §11 instance (11.4) applies it with `(A, B) = (H₁, H₀C)` where neither contains the
other.  The absorption chain then runs over `X = Sa ∪ Sb` from the base `Sa` (Coq: `S1 = S2 ++ S A`
with `S2` the absorbed pairs of `S B`): if every pair of `Sb ∖ Sa` were absorbed coherently the
chain would reach `Sa ∪ Sb` coherent, hence `Sb` coherent by restriction
(`IsCoherent.subset`, with the nonzero supported witness `hne`) — contradiction.  So some pair
breaks, and the break `ψ` lies in `Sb` (the cover's pairs avoid the base `Sa`).

The inclusion-form extractor is `exists_coherentBreakPair_general`
(`S08_CoherenceCorePart1`); this wrapper instantiates it at `Sb := Sa ∪ Sb`. -/
theorem exists_coherentBreakPair_union
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G) {A : Set ↥L}
    {Sa Sb : Set (ClassFunction ↥L ℂ)}
    (hSafin : Sa.Finite) (hSbfin : Sb.Finite)
    (hSaconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sa)
    (hSbconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate Sb)
    (hSareal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sa)
    (hSbreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters Sb)
    (hne : ∃ φ : ClassFunction ↥L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) Sb A ∧ φ ≠ 0)
    (hSacoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sa A))
    (hSbncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ Sb A)) :
    ∃ (S₁ : Set (ClassFunction ↥L ℂ)) (ψ : ClassFunction ↥L ℂ),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ ∧ Sa ⊆ S₁ ∧ S₁ ⊆ Sa ∪ Sb ∧ ψ ∈ Sb ∧
      ψ ∉ S₁ ∧ ψ.conj ∉ S₁ ∧
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A) ∧
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A) := by
  -- the union `Sa ∪ Sb` is finite, conjugation-closed, real-free, and *not* coherent
  -- (else `Sb ⊆ Sa ∪ Sb` would be coherent by restriction).
  have huncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (Sa ∪ Sb) A) := fun h =>
    hSbncoh (h.map (fun hcoh => hcoh.subset Set.subset_union_right hne))
  have hunconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate (Sa ∪ Sb) := fun φ hφ => by
    rcases hφ with hφa | hφb
    · exact Or.inl (hSaconj hφa)
    · exact Or.inr (hSbconj hφb)
  have hunreal : OddOrder.Peterfalvi.S03.HasNoRealCharacters (Sa ∪ Sb) := fun φ hφ => by
    rcases hφ with hφa | hφb
    · exact hSareal hφa
    · exact hSbreal hφb
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁un, hψun, hψnotS₁, hψcnotS₁, hS₁coh, hbreak⟩ :=
    exists_coherentBreakPair_general τ Set.subset_union_left (hSafin.union hSbfin)
      hunconj hunreal hSaconj hSacoh huncoh
  -- the break lies in `Sb`: it avoids `S₁ ⊇ Sa`.
  have hψSb : ψ ∈ Sb := by
    rcases hψun with hψa | hψb
    · exact absurd (hSaS₁ hψa) hψnotS₁
    · exact hψb
  exact ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁un, hψSb, hψnotS₁, hψcnotS₁, hS₁coh, hbreak⟩

section DischargeHelpers

variable [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **The per-member (5.2.d) datum for an *irreducible* member, general discharge.**

For an irreducible member `χ` of a conjugation-closed coherent `S₁` inside the general family,
the `ψ = 0` decomposition `D` with the coherent extension as auxiliary isometry
(`memberExtensionDecomposition`) exists with `D.tau1 χ = ν χ` definitionally — every input
(non-reality, conjugate-difference support, `ν`-integrality, conjugate orthogonality) is
discharged from the family layer.  This reduces the `hdatum` obligation of
`exists_source_index_le_two_psi_of_break` on irreducible members to the *orthogonality* of
`D.imageFamily` against the break's family (grid-side for a reducible break); for reducible
μ-column members the full datum is grid-side (issue 2022). -/
noncomputable def inducedKernelFamily_memberDatum_of_irreducible
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {χ : ClassFunction ↥L ℂ} (hχS₁ : χ ∈ S₁) (hχirr : IsIrreducibleCharacter χ) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        χ 0 //
      D.imageFamily = OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp
        ⟨χ, hχirr⟩ (inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hS₁sub hχS₁))
        (inducedKernelFamily_conjDiff_support hKsupp (hS₁sub hχS₁)) ∧
      D.tau1 χ = hS₁coh.extension χ } := by
  have hχfam : χ ∈ inducedKernelFamily K ⊥ := hS₁sub hχS₁
  have hreal : ¬ ClassFunction.IsReal χ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hχfam
  have hdiffsupp : (χ.conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    inducedKernelFamily_conjDiff_support hKsupp hχfam
  have hχχbar : ClassFunction.inner χ χ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχfam
      (inducedKernelFamily_closedUnderConjugate ⊥ hχfam) (fun h => hreal h.symm)
  have hνZ : hS₁coh.extension χ ∈ ZIrr G :=
    hS₁coh.extension_mem_ZIrr χ (Submodule.subset_span hχS₁)
  exact ⟨memberExtensionDecomposition hyp hS₁coh ⟨χ, hχirr⟩ hreal hdiffsupp
    hχS₁ (hS₁conj hχS₁) hνZ hχχbar, rfl, rfl⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] [K.Normal] in
/-- **`S(X)` is nonempty when `K/X` has proper commutator subgroup** (the `hSBne` discharge):
the anchor lemma's member is in particular a member. -/
theorem inducedKernelFamily_nonempty_of_commutator_ne_top {X : Subgroup ↥L}
    [(X.subgroupOf K).Normal]
    (hXcomm : commutator (↥K ⧸ X.subgroupOf K) ≠ ⊤) :
    (inducedKernelFamily K X).Nonempty := by
  obtain ⟨φ, hφ, -⟩ := exists_inducedKernelFamily_member_degree_index (K := K) hXcomm
  exact ⟨φ, hφ⟩

/-- **The break decomposition `Da` for an *irreducible* break, general discharge.**

For an irreducible break `ψ ∈ S(B)` whose conjugate pair avoids `S₁` (with anchor `χ₁ ∈ S₁` and
degree ratio `a`), the decomposition `Da : CharacterPsiDecomposition τ ψ (a·χ₁)` over the Dade
base map exists with `Da.tau1 = τ` definitionally (`decompositionDaFromDadeOfDiff`); every
input — non-reality, difference supports, `ZIrr`-integrality of `τ(ψ − a·χ₁)`, and the
`ψ, ψ̄ ⊥ a·χ₁` orthogonalities — is discharged from the family layer.  Together with
`inducedKernelFamily_memberDatum_of_irreducible` and
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` this reduces the `hdatum` obligation of
the h56 producer to the pairs involving a *reducible* (μ-column) object. -/
noncomputable def inducedKernelFamily_breakDa_of_irreducible
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψirr : IsIrreducibleCharacter ψ) (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1) :
    { Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        ψ (a • χ₁) //
      Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
        (hyp.fullDadeIsometryData) ∧
      Da.imageFamily = OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp
        ⟨ψ, hψirr⟩
        (inducedKernelFamily_hasNoRealCharacters hodd ⊥ (inducedKernelFamily_subset_bot B hψB))
        (inducedKernelFamily_conjDiff_support hKsupp (inducedKernelFamily_subset_bot B hψB)) }
      := by
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  have hχ₁fam : χ₁ ∈ inducedKernelFamily K ⊥ := hS₁sub hχ₁S₁
  have hreal : ¬ ClassFunction.IsReal ψ :=
    inducedKernelFamily_hasNoRealCharacters hodd ⊥ hψfam
  have hdiffsupp : (ψ.conj - ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    inducedKernelFamily_conjDiff_support hKsupp hψfam
  have hdiffasupp : (ψ - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    inducedKernelFamily_scaledDiff_support hKsupp hψB hχ₁fam (d := a) hψdeg
  have htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData) (ψ - a • χ₁) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp
      hdiffasupp ?_
    exact Submodule.sub_mem _ (inducedKernelFamily_mem_ZIrr hψfam)
      (nsmul_mem (inducedKernelFamily_mem_ZIrr hχ₁fam) a)
  have hψχ₁ : ClassFunction.inner ψ χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hχ₁fam
      (fun h => hψnotS1 (h ▸ hχ₁S₁))
  have hψbarχ₁ : ClassFunction.inner ψ.conj χ₁ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψcfam hχ₁fam
      (fun h => hψcnotS1 (h ▸ hχ₁S₁))
  have hψaχ₁ : ClassFunction.inner ψ (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψχ₁, mul_zero]
  have hψbaraχ₁ : ClassFunction.inner ψ.conj (a • χ₁ : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a χ₁, OddOrder.RepresentationTheory.inner_smul_right,
      hψbarχ₁, mul_zero]
  have hψψbar : ClassFunction.inner ψ ψ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hψfam hψcfam (fun h => hreal h.symm)
  exact ⟨OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp ⟨ψ, hψirr⟩ hreal
    hdiffsupp hdiffasupp htau1_mema hψaχ₁ hψbaraχ₁ hψψbar, rfl, rfl⟩

/-- **The full `hdatum` clause for an irreducible member against an irreducible break** — the
general discharge of the h56 producer's decomposition data on the irreducible–irreducible
diagonal.  For the break decomposition `Da` built by `inducedKernelFamily_breakDa_of_irreducible`
and an *irreducible* member `χ ∈ S₁`, the member decomposition of
`inducedKernelFamily_memberDatum_of_irreducible` is orthogonal to `Da`'s family
(`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` — both image families are the
difference-support Dade `R(·)` families definitionally) and couples to the coherent extension.
After this, the §11-side `hdatum` work is exactly the pairs involving a reducible μ-column
(issue 2022). -/
theorem inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ inducedKernelFamily K ⊥)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {B : Subgroup ↥L} {ψ : ClassFunction ↥L ℂ} (hψB : ψ ∈ inducedKernelFamily K B)
    (hψirr : IsIrreducibleCharacter ψ) (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1)
    {χ : ClassFunction ↥L ℂ} (hχS₁ : χ ∈ S₁) (hχirr : IsIrreducibleCharacter χ) :
    ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        χ 0,
      D.imageFamily.Orthogonal
        (inducedKernelFamily_breakDa_of_irreducible hyp hodd hKsupp hS₁sub hψB hψirr
          hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).1.imageFamily ∧
      D.tau1 χ = hS₁coh.extension χ := by
  set md := inducedKernelFamily_memberDatum_of_irreducible hyp hodd hKsupp
    hS₁sub hS₁conj hS₁coh hχS₁ hχirr with hmd
  set bd := inducedKernelFamily_breakDa_of_irreducible hyp hodd hKsupp hS₁sub hψB hψirr
    hψnotS1 hψcnotS1 hχ₁S₁ hψdeg with hbd
  refine ⟨md.1, ?_, md.2.2⟩
  -- rewrite both image families to the explicit difference-support Dade `R(·)` families,
  -- then apply their orthogonality: the four member–break inner products vanish in the family.
  rw [md.2.1, bd.2.2]
  have hχfam : χ ∈ inducedKernelFamily K ⊥ := hS₁sub hχS₁
  have hχcfam : χ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hχfam
  have hψfam : ψ ∈ inducedKernelFamily K ⊥ := inducedKernelFamily_subset_bot B hψB
  have hψcfam : ψ.conj ∈ inducedKernelFamily K ⊥ :=
    inducedKernelFamily_closedUnderConjugate ⊥ hψfam
  have hχbarS₁ : χ.conj ∈ S₁ := hS₁conj hχS₁
  have hχψ : ClassFunction.inner χ ψ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχfam hψfam
      (fun h => hψnotS1 (h ▸ hχS₁))
  have hχψbar : ClassFunction.inner χ ψ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχfam hψcfam
      (fun h => hψcnotS1 (h ▸ hχS₁))
  have hχbarψ : ClassFunction.inner χ.conj ψ = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχcfam hψfam
      (fun h => hψnotS1 (h ▸ hχbarS₁))
  have hχbarψbar : ClassFunction.inner χ.conj ψ.conj = 0 :=
    inducedKernelFamily_pairwise_orthogonal hχcfam hψcfam
      (fun h => hψcnotS1 (h ▸ hχbarS₁))
  exact dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp
    (inducedKernelFamily_hasNoRealCharacters hodd ⊥ hχfam)
    (inducedKernelFamily_conjDiff_support hKsupp hχfam)
    (inducedKernelFamily_hasNoRealCharacters hodd ⊥ hψfam)
    (inducedKernelFamily_conjDiff_support hKsupp hψfam)
    hχψ hχψbar hχbarψ hχbarψbar

end DischargeHelpers

section H56Producer

variable [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

open scoped Classical in
/-- **The (6.2) break bound `|K:A'| − 1 ≤ 2ψ(1)` from Hypothesis (5.2) data, abstract `τ`.**

The `τ`-general form of `exists_source_index_le_two_psi_of_break` (issue 0154): no Feit–Thompson
Dade map, only an integral `τ` satisfying the two clauses of Peterfalvi **Hypothesis (5.2.b)** on
the `A₀`-supported sublattice of `ℤ[𝒮]` (`hisom`, `htauZ`), plus the (5.2.d)/(5.2.e) decomposition
data `hdatum` at each break.

From the coherence dichotomy `S(A')` coherent / `S(B)` not, the first-obstruction chain
(`exists_coherentBreakPair_union`, already `τ`-general) produces a break pair `{ψ, ψ̄} ⊆ S(B)` over
a maximal coherent conjugation-closed `S₁ ⊆ S(A') ∪ S(B)`; the norm-weighted (5.6) contrapositive
bounds the `S(A')` degree-square sum, and the (B2) identity converts it into the index bound.  The
Feit–Thompson wrapper is `exists_source_index_le_two_psi_of_break`. -/
theorem exists_source_index_le_two_psi_of_break_general
    {A₀ : Set ↥L}
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]
    (hisom : ∀ ⦃φ ζ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ζ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (htauZ : ∀ ⦃φ : ClassFunction ↥L ℂ⦄,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ →
      τ φ ∈ ZIrr G)
    (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    (h1A : (1 : ↥L) ∉ A₀)
    {A' B : Subgroup ↥L} [A'.Normal]
    (hanchor : ∃ χ₁ ∈ inducedKernelFamily K A', χ₁ 1 = (K.index : ℂ))
    (hSBne : (inducedKernelFamily K B).Nonempty)
    (hdatum : ∀ (S₁ : Set (ClassFunction ↥L ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ inducedKernelFamily K A' ∪ inducedKernelFamily K B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A₀),
      ∀ (ψ : ClassFunction ↥L ℂ), ψ ∈ inducedKernelFamily K B → ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥L ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (S₁ ∪ {ψ, ψ.conj}) A₀) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ ψ (a • χ₁),
        Da.tau1 = τ ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
            τ χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (inducedKernelFamily K A') A₀))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (inducedKernelFamily K B) A₀)) :
    ∃ θ : IrreducibleCharacter ↥K,
      (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥K ℂ) ∧
      (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
        2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re := by
  classical
  obtain ⟨χ₁, hχ₁A', hχ₁deg⟩ := hanchor
  -- the nonzero supported witness for `ℤ[S(B)]`: a conjugate difference of any member.
  obtain ⟨φ₀, hφ₀⟩ := hSBne
  have hne : ∃ φ : ClassFunction ↥L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K B) A₀ ∧
        φ ≠ 0 := by
    refine ⟨φ₀.conj - φ₀, ?_, ?_⟩
    · refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, ?_⟩
      · exact Submodule.sub_mem _
          (Submodule.subset_span (inducedKernelFamily_closedUnderConjugate B hφ₀))
          (Submodule.subset_span hφ₀)
      · exact inducedKernelFamily_conjDiff_support hKsupp hφ₀
    · intro h
      exact inducedKernelFamily_hasNoRealCharacters hodd B hφ₀ (sub_eq_zero.mp h)
  -- the first-obstruction break pair over `S(A') ∪ S(B)`.
  obtain ⟨S₁, ψ, hS₁conj, hSaS₁, hS₁un, hψB, hψnotS₁, hψcnotS₁, hS₁coh, hbreak⟩ :=
    exists_coherentBreakPair_union τ
      (inducedKernelFamily_finite A') (inducedKernelFamily_finite B)
      (inducedKernelFamily_closedUnderConjugate A')
      (inducedKernelFamily_closedUnderConjugate B)
      (inducedKernelFamily_hasNoRealCharacters hodd A')
      (inducedKernelFamily_hasNoRealCharacters hodd B)
      hne hAcoh hBncoh
  -- fixed coherence witness for `S₁` (the datum couples to its extension).
  obtain ⟨hcoh⟩ := hS₁coh
  -- `S₁` sits inside the full family and is finite.
  have hS₁bot : S₁ ⊆ inducedKernelFamily K ⊥ := fun χ hχ => by
    rcases hS₁un hχ with h | h
    · exact inducedKernelFamily_subset_bot A' h
    · exact inducedKernelFamily_subset_bot B h
  have hS₁fin : S₁.Finite :=
    ((inducedKernelFamily_finite (K := K) A').union (inducedKernelFamily_finite B)).subset hS₁un
  -- the break's degree ratio against the anchor.
  obtain ⟨a, hapos, haeq⟩ := inducedKernelFamily_degree_ratio (inducedKernelFamily_subset_bot B hψB)
  have hψdeg : ψ 1 = (a : ℂ) * χ₁ 1 := by rw [haeq, hχ₁deg]
  -- the (5.2.d)/(5.2.e)-backed decomposition data at this break.
  obtain ⟨Da, hDatau1, hdat⟩ := hdatum S₁ hS₁conj hS₁un hcoh ψ hψB hψnotS₁ hψcnotS₁
    χ₁ (hSaS₁ hχ₁A') a hψdeg hbreak
  -- the (6.2) `S(A')`-sum bound at the break.
  have hbound := inducedKernelFamily_SA_sum_le_two_psi_k_general τ hisom htauZ hodd hKsupp h1A
    hS₁bot hS₁fin hcoh hSaS₁ (hSaS₁ hχ₁A') hχ₁deg hψB hψnotS₁ hψcnotS₁ hψdeg
    Da hDatau1
    (fun χ hχ => ⟨(hdat χ hχ).choose, (hdat χ hχ).choose_spec⟩)
    hbreak
  -- divide by the positive anchor degree `χ₁(1) = |L:K|`.
  have hKidx_pos : (0 : ℝ) < (K.index : ℝ) := by
    rw [Subgroup.index_eq_card]
    exact_mod_cast Nat.card_pos
  have hχ₁re : (χ₁ 1).re = (K.index : ℝ) := by
    rw [hχ₁deg, Complex.natCast_re]
  rw [hχ₁re] at hbound
  have hdiv : (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤ 2 * (ψ 1).re := by
    have h2 : (K.index : ℝ) * ((Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1)
        ≤ (K.index : ℝ) * (2 * (ψ 1).re) := by
      calc (K.index : ℝ) * ((Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1)
          ≤ 2 * (ψ 1).re * (K.index : ℝ) := hbound
        _ = (K.index : ℝ) * (2 * (ψ 1).re) := by ring
    exact le_of_mul_le_mul_left h2 hKidx_pos
  -- unpack the break's source `θ` (trivial on `B`).
  obtain ⟨θ, -, hθker, hψeq⟩ := hψB
  refine ⟨θ, hθker, ?_⟩
  rw [← hψeq]
  exact hdiv

/-- **The (6.2) index bound `|K:A'| − 1 ≤ 2ψ(1)` at a break member — the `h56` producer**
(issue 2022; Coq `coherent_seqIndD_bound`, contrapositive route).

Given the general induced families `S(A')` (coherent) and `S(B)` (not coherent) over a kernel
`K ≤ L` — **no inclusion between `A'` and `B` is assumed** (Peterfalvi (11.4) needs
`(A', B) = (H₁, H₀C)` incomparable) — together with

* an **anchor**: a member `χ₁ ∈ S(A')` of the minimal degree `|L:K|` — **no irreducibility**,
  exactly as Peterfalvi (6.2) states it ("Since `K` is solvable, `K/A` has a non-trivial
  irreducible character of degree 1, whence `S(A)` contains a character of degree `|L:K|`", p. 30).
  Discharged in general by `exists_inducedKernelFamily_member_degree_index` from
  `commutator (K ⧸ A'.subgroupOf K) ≠ ⊤`; the (5.6) engine carries `‖χ₁‖²` symbolically
  (`crux1_of_memberFamilyW`), so no inertia condition on the linear source is needed, and
* the **(5.2.d) decomposition data** `hdatum` for any intermediate coherent set and break pair:
  the break's decomposition `Da` over the Dade map and, per member `χ` of the coherent set, an
  `R(χ)`-decomposition compatible with the coherent extension and orthogonal to `Da`'s family.
  Two discharges exist: in general from Hypothesis (5.2)'s image families
  (`S08.InducedFamilyImageData.datum`, `S08_SixTwoThreeFromImageFamilies`, issue 0153), and in the
  concrete §11/§13 context from the muGrid columns (`S12.Hypothesis.sixTwoDecompositionData`,
  `S13_SixTwoBridge`),

the first-obstruction chain (`exists_coherentBreakPair_union`) produces a break `ψ ∈ S(B)`
with `|K:A'| − 1 ≤ 2·ψ(1)`; unpacking `ψ = Ind_K^L θ` gives exactly the `h56` oracle of
`six_three_of_six_two_oracle`/`six_two_general` (`S08_Theorem62_63_Standalone`): a source
`θ ∈ Irr K` trivial on `B` whose induced degree bounds the index.  Everything outside `hdatum`
and the anchor is discharged by the general family layer of this file. -/
theorem exists_source_index_le_two_psi_of_break
    {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hodd : Odd (Nat.card ↥L))
    {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {A' B : Subgroup ↥L} [A'.Normal]
    (hanchor : ∃ χ₁ ∈ inducedKernelFamily K A', χ₁ 1 = (K.index : ℂ))
    (hSBne : (inducedKernelFamily K B).Nonempty)
    (hdatum : ∀ (S₁ : Set (ClassFunction ↥L ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ inducedKernelFamily K A' ∪ inducedKernelFamily K B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L)),
      ∀ (ψ : ClassFunction ↥L ℂ), ψ ∈ inducedKernelFamily K B → ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥L ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
        (S₁ ∪ {ψ, ψ.conj}) (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
            (hyp.fullDadeIsometryData)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
          (hyp.fullDadeIsometryData) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
              (hyp.fullDadeIsometryData)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K A') (OddOrder.Peterfalvi.S04.supportInSubgroup A L)))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (inducedKernelFamily K B) (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∃ θ : IrreducibleCharacter ↥K,
      (↑(B.subgroupOf K) : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥K ℂ) ∧
      (Nat.card (↥K ⧸ A'.subgroupOf K) : ℝ) - 1 ≤
        2 * (ClassFunction.induce K (θ : ClassFunction ↥K ℂ) 1).re :=
  -- The Feit-Thompson instance of the `τ`-general statement: (5.2.b) is the Dade isometry plus
  -- its `ℤ[Irr G]` codomain on `A₀`-supported elements of `ℤ[𝒮]`.
  exists_source_index_le_two_psi_of_break_general
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    (fun _φ _ζ hφ hζ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
        (S := OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥)
          (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
        (fun _s hs => hs.2) (Submodule.subset_span hφ) (Submodule.subset_span hζ))
    (fun _φ hφ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp hφ.2
        (Submodule.span_le.mpr (fun _x hx => inducedKernelFamily_mem_ZIrr hx) hφ.1))
    hodd hKsupp h1A hanchor hSBne hdatum hAcoh hBncoh

end H56Producer

end OddOrder.Peterfalvi.S08


