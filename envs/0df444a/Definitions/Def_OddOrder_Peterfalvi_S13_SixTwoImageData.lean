-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoImageData
-- name    : OddOrder_Peterfalvi_S13_SixTwoImageData
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:36:37.044709+00:00
-- url     : https://prove2.me/theorems/c8809a36-1d7a-484f-9449-4de1b92de961
-- title:
--   Peterfalvi (5.2.d)/(5.2.e): image data for the §11 induced family
-- statement:
--   Formalizes the (5.2.d)/(5.2.e) image data for the §11 induced family (Peterfalvi, *Character Theory for the Odd Order Theorem*, §5 (5.2)/(5.3.b), §6 (6.1), §10-§11): column indices of members and their orthonormal signed Dade families.
--
--   Main declarations: `memberColumn` (The column index of a reducible member); `memberColumnConj` (The conjugate column of a reducible member); `irrRFamily` ((5.2.d) for an irreducible member); `colRFamily` ((5.2.d) for a reducible member).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_SixTwoImageData.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_SixTwoImageData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoBridge
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoThreeFromImageFamilies

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open OddOrder.GroupTheory

open scoped FiniteInduce

variable {G : Type*} [Group G] {M : Subgroup G}

namespace Hypothesis

section ColumnIndex

variable [Finite G]

/-- **The column index of a reducible member** (Peterfalvi (5.3.b), via (4.4)/(4.5)): a member of
the §11 induced family `S(⊥)` that is not irreducible is a nonzero μ-grid column sum, and this is
its column.  Chosen once and for all so the (5.2.d) family below is a genuine function of `χ`. -/
noncomputable def memberColumn (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) : Fin hyp.w2 :=
  (hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG hχ hred).choose

theorem memberColumn_ne_zero (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) : hyp.memberColumn hG hχ hred ≠ 0 :=
  (hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG hχ hred).choose_spec.1

theorem eq_columnSum_memberColumn (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    χ = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i (hyp.memberColumn hG hχ hred) :=
  (hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG hχ hred).choose_spec.2

/-- **The conjugate column of a reducible member** (Peterfalvi (4.9)(a) `μ̄_j = μ_k`). -/
noncomputable def memberColumnConj (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) : Fin hyp.w2 :=
  (hyp.exists_conj_column hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred)).choose

theorem memberColumnConj_ne_zero (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) : hyp.memberColumnConj hG hχ hred ≠ 0 :=
  (hyp.exists_conj_column hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred)).choose_spec.1

theorem memberColumnConj_ne (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    hyp.memberColumnConj hG hχ hred ≠ hyp.memberColumn hG hχ hred :=
  (hyp.exists_conj_column hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred)).choose_spec.2.1

/-- The conjugate-column identity at the member's own columns (Peterfalvi (4.9)(a)). -/
theorem columnSum_memberColumn_conj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis M) {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i (hyp.memberColumn hG hχ hred)).conj
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i (hyp.memberColumnConj hG hχ hred) :=
  (hyp.exists_conj_column hG hG.odd (hyp.memberColumn_ne_zero hG hχ hred)).choose_spec.2.2

theorem conj_eq_columnSum_memberColumnConj (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis M) {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    χ.conj = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i (hyp.memberColumnConj hG hχ hred) :=
  (congrArg ClassFunction.conj (hyp.eq_columnSum_memberColumn hG hχ hred)).trans
    (hyp.columnSum_memberColumn_conj hG hχ hred)

end ColumnIndex

section RFamily

variable [Finite G]

/-- **The norm-`2` conjugate-difference image of an irreducible member.**  For an irreducible
`χ ∈ S(⊥)`, `‖τ(χ − χ̄)‖² = ‖χ − χ̄‖² = 2` — the Dade map is an isometry on the `A₀`-supported
difference (`inducedKernelFamily_conjDiff_support`), and `χ ⊥ χ̄` with both of norm `1`.  This is
the `hT2` input of `OrthonormalCharacterImageFamily.elt_inner_eq_zero`. -/
theorem tau_conjDiff_inner_self_eq_two (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis M) {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hirr : IsIrreducibleCharacter χ) :
    ClassFunction.inner (hyp.tau (χ - χ.conj)) (hyp.tau (χ - χ.conj)) = 2 := by
  have := hyp.finiteG
  have hModd : Odd (Nat.card ↥M) := hyp.card_odd_of_isMinimalSimpleOdd hG
  have hχconj : χ.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate ⊥ hχ
  have hnr : χ.conj ≠ χ :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hχ
  have hsupp : (χ - χ.conj).support ⊆ hyp.A0 := by
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.mderivSharp_subset_A0 hχ
    rw [show χ - χ.conj = -(χ.conj - χ) from by abel, ClassFunction.support_neg]
    exact h
  have hset : ∀ s ∈ ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆ hyp.A0 := by
    rintro s rfl; exact hsupp
  have hmem : χ - χ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
  have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hset hmem hmem
  rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) from rfl, hpres,
    ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right]
  have h11 : ClassFunction.inner χ χ = 1 := by
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨χ, hirr⟩ : IrreducibleCharacter ↥M) ⟨χ, hirr⟩
  have hcc : ClassFunction.inner χ.conj χ.conj = 1 := by
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨χ.conj, hirr.conj⟩ : IrreducibleCharacter ↥M) ⟨χ.conj, hirr.conj⟩
  have hcr : ClassFunction.inner χ χ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχ hχconj (Ne.symm hnr)
  have hcr' : ClassFunction.inner χ.conj χ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχconj hχ hnr
  rw [h11, hcc, hcr, hcr']
  ring

/-- **(5.2.d) for an irreducible member**: the two-element signed Dade family
`R(χ) = {ε·μ, −ε·ν}` (Peterfalvi (5.3.a): `‖(χ − χ̄)^τ‖² = 2`, so `|R(χ)| = 2`). -/
noncomputable def irrRFamily (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hirr : IsIrreducibleCharacter χ) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau χ :=
  OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
    ⟨χ, hirr⟩
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hyp.card_odd_of_isMinimalSimpleOdd hG) ⊥ hχ)
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.mderivSharp_subset_A0 hχ)

/-- **(5.2.d) for a reducible member** (Peterfalvi (5.3.b) via Theorem (4.9)): the column family
`R(μ_j) = {δ ω_{ij}^σ, −δ ω_{ij'}^σ | 0 ≤ i < w₁}` of the §10 μ-grid, transported from the column
`∑ᵢ μ_{ij}` to the member `χ` it equals. -/
noncomputable def colRFamily (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau χ :=
  OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily.congrChi
    (hyp.eq_columnSum_memberColumn hG hχ hred)
    (hyp.columnImageFamilyCohFree hG hmu hzS hz1 hzconj hδpm hδj
      (hyp.memberColumn_ne_zero hG hχ hred) (hyp.memberColumnConj_ne_zero hG hχ hred)
      (Ne.symm (hyp.memberColumnConj_ne hG hχ hred))
      (hyp.columnSum_memberColumn_conj hG hχ hred))

open scoped Classical in
/-- **The (5.2.d) family of a §11 member** — the dispatch of Peterfalvi (5.3.b): the two-element
Dade family on the irreducible members, the μ-grid column family on the reducible ones. -/
noncomputable def memberRFamily (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M)) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.tau χ :=
  if hirr : IsIrreducibleCharacter χ then hyp.irrRFamily hG hχ hirr
  else hyp.colRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ hirr

open scoped Classical in
theorem memberRFamily_of_irr (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hirr : IsIrreducibleCharacter χ) :
    hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ = hyp.irrRFamily hG hχ hirr :=
  dif_pos hirr

open scoped Classical in
theorem memberRFamily_of_red (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ
      = hyp.colRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ hred :=
  dif_neg hred

open scoped Classical in
/-- The reducible branch's `imageSet` is the signed σ-grid column pair. -/
theorem colRFamily_imageSet (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hred : ¬ IsIrreducibleCharacter χ) :
    (hyp.colRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ hred).imageSet
      = Finset.univ.image (hyp.columnRImage hG hG.odd params.delta
          (hyp.memberColumn hG hχ hred) (hyp.memberColumnConj hG hχ hred)) := rfl

end RFamily

section Orthogonality

variable [Finite G]

/-- **Every `R(χ)`-element of an irreducible member is orthogonal to the whole σ-grid.**  The
image `τ(χ − χ̄)` has norm `2` and is orthogonal to each `ω_{ij}^σ`
(`tau_chidiff_inner_alignedOmega_eq_zero`), so the integrality/Cauchy–Schwarz argument of
`OrthonormalCharacterImageFamily.elt_inner_eq_zero` forces every summand of `τ(χ − χ̄)` to be
orthogonal to `ω_{ij}^σ` as well.  This is the shared engine of the two mixed (5.2.e) cases. -/
theorem irrRFamily_inner_alignedOmega_eq_zero (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis M) {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hirr : IsIrreducibleCharacter χ)
    {α : ClassFunction G ℂ} (hα : α ∈ (hyp.irrRFamily hG hχ hirr).imageSet)
    (i : Fin hyp.w1) (k : Fin hyp.w2) :
    ClassFunction.inner α (hyp.alignedOmegaSigmaGrid hG hG.odd i k) = 0 := by
  have := hyp.finiteG
  have hχind : χ ∈ inducedFamily M := by
    rw [inducedFamily_eq_inducedKernelFamily_bot]; exact hχ
  refine OddOrder.Peterfalvi.S12.OrthonormalCharacterImageFamily.elt_inner_eq_zero
    (R := hyp.irrRFamily hG hχ hirr) hα
    (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i k) ?_ ?_ ?_
  · simpa using hyp.alignedOmegaSigmaGrid_inner hG hG.odd i i k k
  · exact hyp.tau_conjDiff_inner_self_eq_two hG hχ hirr
  · exact hyp.tau_chidiff_inner_alignedOmega_eq_zero hG hG.odd hχind hirr i k

open scoped Classical in
/-- **Peterfalvi (5.2.e) for the §11 family**: two members orthogonal in the sense
`φ ⊥ {χ, χ̄}` have orthogonal difference-image families `R(φ) ⊥ R(χ)`.

The four cases of (5.3.b)'s proof.  *irr × irr* is (4.1)
(`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`, needing all four cross inner products,
which follow from `φ ≠ χ, χ̄` and `φ̄ ≠ χ, χ̄` by the family's pairwise orthogonality).  The two
*mixed* cases go through `irrRFamily_inner_alignedOmega_eq_zero` ("`R(φ)` is orthogonal to `ω^σ`
for all `ω ∈ Irr W`" — Peterfalvi's `NC((φ − φ̄)^τ) ≤ 2` argument via (3.8)).  *col × col* is "the
form of `R(μ_j)`": the four column indices `k_φ, k_φ', k_χ, k_χ'` are pairwise distinct because
`φ ≠ χ, χ̄`, so the σ-grid orthonormality kills every cross pair. -/
theorem memberRFamily_orthogonal (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    {χ φ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
      (⊥ : Subgroup ↥M))
    (hφχ : ClassFunction.inner φ χ = 0) (hφχbar : ClassFunction.inner φ χ.conj = 0) :
    (hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hφ).Orthogonal
      (hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ) := by
  have := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hyp.card_odd_of_isMinimalSimpleOdd hG
  set K := (derivedInG M).subgroupOf M with hK
  have hχc : χ.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate ⊥ hχ
  have hφc : φ.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate ⊥ hφ
  -- `φ ≠ χ` and `φ ≠ χ̄` from the orthogonality hypotheses (members have nonzero norm).
  have hne : φ ≠ χ := by
    rintro rfl
    exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hφ).2.ne'
      (by rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hφ).1] at hφχ
          exact_mod_cast hφχ)
  have hnec : φ ≠ χ.conj := by
    rintro rfl
    exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hφ).2.ne'
      (by rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hφ).1] at hφχbar
          exact_mod_cast hφχbar)
  -- the two remaining cross inner products (`φ̄` against `χ`, `χ̄`)
  have hφbarχ : ClassFunction.inner φ.conj χ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hφc hχ (fun h => by
      apply hnec
      rw [← h, ClassFunction.conj_conj])
  have hφbarχbar : ClassFunction.inner φ.conj χ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hφc hχc (fun h => by
      apply hne
      have := congrArg ClassFunction.conj h
      rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at this)
  -- the σ-grid cross-orthogonality used by the column cases
  have hcross : ∀ (i i' : Fin hyp.w1) (κ κ' : Fin hyp.w2), κ ≠ κ' →
      ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i κ)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i' κ') = 0 := by
    intro i i' κ κ' hκ
    rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i i' κ κ', if_neg (fun hh => hκ hh.2)]
  by_cases hφirr : IsIrreducibleCharacter φ
  · rw [hyp.memberRFamily_of_irr hG hmu hδpm hδj hzS hz1 hzconj hφ hφirr]
    by_cases hχirr : IsIrreducibleCharacter χ
    · -- irr × irr
      rw [hyp.memberRFamily_of_irr hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr]
      exact OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
        hyp.dadeData.dade _ _ _ _ hφχ hφχbar hφbarχ hφbarχbar
    · -- irr × col: kill each `R(φ)`-element against each signed σ-grid vector
      rw [hyp.memberRFamily_of_red hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr]
      intro α hα β hβ
      rw [hyp.colRFamily_imageSet hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr,
        Finset.mem_image] at hβ
      obtain ⟨⟨b, i⟩, -, rfl⟩ := hβ
      rcases b with _ | _ <;>
        simp only [Hypothesis.columnRImage] <;>
        rw [OddOrder.RepresentationTheory.inner_smul_right,
          hyp.irrRFamily_inner_alignedOmega_eq_zero hG hφ hφirr hα, mul_zero]
  · rw [hyp.memberRFamily_of_red hG hmu hδpm hδj hzS hz1 hzconj hφ hφirr]
    by_cases hχirr : IsIrreducibleCharacter χ
    · -- col × irr: conjugate-symmetry of the mixed case
      rw [hyp.memberRFamily_of_irr hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr]
      intro α hα β hβ
      rw [hyp.colRFamily_imageSet hG hmu hδpm hδj hzS hz1 hzconj hφ hφirr,
        Finset.mem_image] at hα
      obtain ⟨⟨b, i⟩, -, rfl⟩ := hα
      have hωβ : ∀ (i' : Fin hyp.w1) (κ : Fin hyp.w2),
          ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i' κ) β = 0 := by
        intro i' κ
        rw [OddOrder.RepresentationTheory.inner_conj_symm,
          hyp.irrRFamily_inner_alignedOmega_eq_zero hG hχ hχirr hβ, star_zero]
      rcases b with _ | _
      · simp only [Hypothesis.columnRImage]
        rw [ClassFunction.inner_smul_left, hωβ, mul_zero]
      · simp only [Hypothesis.columnRImage]
        rw [neg_smul, ClassFunction.inner_neg_left, ClassFunction.inner_smul_left, hωβ,
          mul_zero, neg_zero]
    · -- col × col: the four column indices are pairwise distinct
      rw [hyp.memberRFamily_of_red hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr]
      have hcolφ := hyp.eq_columnSum_memberColumn hG hφ hφirr
      have hcolφc := hyp.conj_eq_columnSum_memberColumnConj hG hφ hφirr
      have hcolχ := hyp.eq_columnSum_memberColumn hG hχ hχirr
      have hcolχc := hyp.conj_eq_columnSum_memberColumnConj hG hχ hχirr
      have h1 : hyp.memberColumn hG hφ hφirr ≠ hyp.memberColumn hG hχ hχirr := by
        intro he; exact hne (by rw [hcolφ, he, ← hcolχ])
      have h2 : hyp.memberColumn hG hφ hφirr ≠ hyp.memberColumnConj hG hχ hχirr := by
        intro he; exact hnec (by rw [hcolφ, he, ← hcolχc])
      have h3 : hyp.memberColumnConj hG hφ hφirr ≠ hyp.memberColumn hG hχ hχirr := by
        intro he
        apply hnec
        have : φ.conj = χ := by rw [hcolφc, he, ← hcolχ]
        rw [← this, ClassFunction.conj_conj]
      have h4 : hyp.memberColumnConj hG hφ hφirr ≠ hyp.memberColumnConj hG hχ hχirr := by
        intro he
        apply hne
        have hcc : φ.conj = χ.conj := by rw [hcolφc, he, ← hcolχc]
        have := congrArg ClassFunction.conj hcc
        rwa [ClassFunction.conj_conj, ClassFunction.conj_conj] at this
      intro α hα β hβ
      rw [hyp.colRFamily_imageSet hG hmu hδpm hδj hzS hz1 hzconj hφ hφirr,
        Finset.mem_image] at hα
      rw [hyp.colRFamily_imageSet hG hmu hδpm hδj hzS hz1 hzconj hχ hχirr,
        Finset.mem_image] at hβ
      obtain ⟨⟨bα, iα⟩, -, rfl⟩ := hα
      obtain ⟨⟨bβ, iβ⟩, -, rfl⟩ := hβ
      rcases bα with _ | _ <;> rcases bβ with _ | _ <;>
        simp only [Hypothesis.columnRImage] <;>
        rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
      · rw [hcross _ _ _ _ h1, mul_zero, mul_zero]
      · rw [hcross _ _ _ _ h2, mul_zero, mul_zero]
      · rw [hcross _ _ _ _ h3, mul_zero, mul_zero]
      · rw [hcross _ _ _ _ h4, mul_zero, mul_zero]

end Orthogonality

section Bundle

variable [Finite G]

/-- **Hypothesis (5.2.d)/(5.2.e) for the §11 induced family** — the `InducedFamilyImageData`
instance, i.e. the concrete witness that the book's (6.1) hypotheses are satisfiable in the
Feit–Thompson setting.  Exactly Peterfalvi (5.3.b): irreducible members get the two-element Dade
family, reducible ones the μ-grid column family `R(μ_j)` of Theorem (4.9). -/
noncomputable def inducedFamilyImageData (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis M) {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta) :
    OddOrder.Peterfalvi.S08.InducedFamilyImageData hyp.A0
      ((derivedInG M).subgroupOf M) where
  tau := hyp.tau
  -- (5.2.b): the Dade isometry, and its `ℤ[Irr G]` codomain, on `A₀`-supported elements of `ℤ[𝒮]`
  -- (`hφ.1 : φ ∈ ℤ[𝒮]`, `hφ.2 : supp φ ⊆ A₀`; `ℤ[𝒮] ≤ ℤ[Irr M]` since every member is a character).
  tau_isometry := fun _φ _ζ hφ hζ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dadeData.dade
      (S := OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M)
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥) hyp.A0)
      (fun _s hs => hs.2) (Submodule.subset_span hφ) (Submodule.subset_span hζ)
  tau_mem_ZIrr := fun _φ hφ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dadeData.dade hφ.2
      (Submodule.span_le.mpr
        (fun _x hx => OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hx) hφ.1)
  -- (5.2.b) codomain sharpness: the Dade image vanishes off the Dade support, in particular at `1`.
  tau_apply_one := fun _φ hφ =>
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero hyp.dadeData.dade hφ.2
  R := fun _χ hχ => hyp.memberRFamily hG hmu hδpm hδj hzS hz1 hzconj hχ
  orthogonal := fun _χ hχ _φ hφ hφχ hφχbar =>
    hyp.memberRFamily_orthogonal hG hmu hδpm hδj hzS hz1 hzconj hχ hφ hφχ hφχbar

/-- **Peterfalvi (6.2) for the §11 context, from Hypothesis (5.2) data only** — no `h56` oracle.
For a section `B ≤ D ≤ C ≤ M'` with `D/B` central in `C/B`, and proper traces `A', B ⊊ M'`, the
coherence dichotomy `S(A')` coherent / `S(B)` not gives `|M':A'| − 1 ≤ 2|M:C|·√|C:D|`.  This is
`S08.six_two_of_imageData` pinned to `S12.Hypothesis M`; the (11.4) instance takes
`(C, D) = (HC, HC)` (`√1 = 1`) and the (11.3)/(6.3) route `(C, D) = (HC, A')`. -/
theorem sixTwo_of_hypothesis (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    {A' B C D : Subgroup ↥M} [A'.Normal] [B.Normal]
    (hA'K : A' < (derivedInG M).subgroupOf M) (hBK : B < (derivedInG M).subgroupOf M)
    (hBD : B ≤ D) (hCK : C ≤ (derivedInG M).subgroupOf M)
    (hcentral : (D.subgroupOf C).map (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (↥C ⧸ B.subgroupOf C))
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A') hyp.A0))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B) hyp.A0)) :
    (Nat.card (↥((derivedInG M).subgroupOf M) ⧸
        A'.subgroupOf ((derivedInG M).subgroupOf M)) : ℝ) - 1 ≤
      2 * (C.index : ℝ) * Real.sqrt (Nat.card (↥C ⧸ D.subgroupOf C) : ℝ) := by
  have := hyp.finiteG
  have : Fintype ↥C := Fintype.ofFinite _
  have : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have : Group.IsSolvable ↥M := hG.isSolvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.maximal.1)
  have : Group.IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  exact OddOrder.Peterfalvi.S08.six_two_of_imageData
    (hyp.inducedFamilyImageData hG hmu hδpm hδj hzS hz1 (hyp.zeta_conj_ne hG hz1))
    (hyp.card_odd_of_isMinimalSimpleOdd hG) hyp.mderivSharp_subset_A0 hyp.one_notMem_A0
    hA'K hBK hBD hCK hcentral hAcoh hBncoh

/-- **Peterfalvi (6.3) for the §11 context, from Hypothesis (5.2) data only** — no `h56`/`h62`
oracle: the break bound is *proved* from the (5.2.d)/(5.2.e) families of
`inducedFamilyImageData`.  This is `S08.six_three_of_imageData` pinned to `S12.Hypothesis M`
(kernel `K = M'`, `τ = hyp.tau`, `A₀ = hyp.A0`). -/
theorem sixThree_of_hypothesis (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    {H N H₁ : Subgroup ↥M} [Group.IsNilpotent ↥H] [N.Normal] [H₁.Normal]
    (hHnorm : H.Normal) (hNH₁ : N ≤ H₁) (hH₁H : H₁ < H)
    (hHK : H ≤ (derivedInG M).subgroupOf M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) H₁) hyp.A0))
    (hbound : 4 * ((derivedInG M).subgroupOf M).index ^ 2 + 1
      < Nat.card (↥H ⧸ H₁.subgroupOf H)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) N) hyp.A0) := by
  have := hyp.finiteG
  have : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  -- (6.1) "`K` is a solvable normal subgroup of `L`": `M` is a proper subgroup of the
  -- minimal simple `G`, hence solvable, and `M' ≤ M`.
  have : Group.IsSolvable ↥M := hG.isSolvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.maximal.1)
  have : Group.IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  exact OddOrder.Peterfalvi.S08.six_three_of_imageData
    (hyp.inducedFamilyImageData hG hmu hδpm hδj hzS hz1 (hyp.zeta_conj_ne hG hz1))
    (hyp.card_odd_of_isMinimalSimpleOdd hG) hyp.mderivSharp_subset_A0 hyp.one_notMem_A0
    hHnorm hNH₁ hH₁H hHK hcoh hbound

end Bundle

end Hypothesis

end OddOrder.Peterfalvi.S12


