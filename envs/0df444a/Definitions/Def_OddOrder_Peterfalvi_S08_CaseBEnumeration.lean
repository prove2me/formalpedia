-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEnumeration
-- name    : OddOrder_Peterfalvi_S08_CaseBEnumeration
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:18:40.469337+00:00
-- url     : https://prove2.me/theorems/2bf0a76a-0372-4ba2-aadd-bed970ac1847
-- title:
--   Peterfalvi (6.8.2): case-(B) conjugate-pair cover of the $X$-set
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.8.2). This file produces the case-(B) conjugate-pair cover of the $X$-set $X(W_2)$, with base the certain-type column set, in the four-conjunct form consumed by the norm-weighted $X$-chain fold.
--
--   Main definitions: `caseB_member_orthoDatum` (the per-member (5.4) decomposition bundled with its (5.2.e) cross-orthogonality) and the column-break variant `caseB_member_orthoDatum_columnBreak`.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBEnumeration.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBEnumeration.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBHortho
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceWeighted

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **The case-(B) `X`-set contains no real characters** (`hXreal` for the case-(B) cover).  By the
`S`-level cover (`caseB_induce_column_or_irreducible`) each `X(W₂)`-member is either a certain-type
column or an irreducible `Ind^L_H θ`:

* **column** `χ = columnSum h46 χ₂` (`χ₂ ≠ 1`): its conjugate is the inverse column
  `columnSum h46 χ₂⁻¹` (`columnSum_conj_eq`) with `χ₂⁻¹ ≠ χ₂` (`column_inv_ne_self`), so the
  conjugate differs by the column Gram matrix (`⟨χ, χ⟩ = w₁ ≠ 0 = ⟨χ, χ̄⟩`,
  `columnFamily_mu_sum_inner`, `w₁ = Nat.card W₁ ≠ 0`);
* **irreducible** `Ind^L_H θ`: non-real because `L` has odd order (`caseB_irr_nonreal`). -/
theorem Xset_hasNoRealCharacters_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset h46.W2) := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  intro χ hχX
  -- An `X(W₂)`-member is an induced character `Ind^L_H θ` with `θ ≠ 1`.
  have hχS : χ ∈ hyp.S := hyp.Xset_subset_S hχX
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hχS
  obtain ⟨θ, hθne, rfl⟩ := hχS
  have hθne' : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hθne (Subtype.ext (heq.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm))
  rcases caseB_induce_column_or_irreducible h46 hHK hθne' with ⟨χ₂, hχ₂, hcol⟩ | hirr
  · -- column branch: distinct from its inverse column by the Gram matrix.
    intro hreal
    rw [ClassFunction.IsReal, ← hcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq] at hreal
    -- `columnSum χ₂⁻¹ = columnSum χ₂` would force `w₁ = 0` via the Gram entries.
    have hgram_self := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂
    have hgram_cross := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂⁻¹
    rw [if_pos rfl] at hgram_self
    rw [if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂).symm] at hgram_cross
    -- `⟨columnSum χ₂, columnSum χ₂⟩ = ⟨columnSum χ₂, columnSum χ₂⁻¹⟩`, i.e. `w₁ = 0`.
    simp only [← OddOrder.Peterfalvi.S06.columnSum_def] at hgram_self hgram_cross
    rw [hreal] at hgram_cross
    have hcontra : (Nat.card h46.W1 : ℂ) = 0 := hgram_self.symm.trans hgram_cross
    have hne : Nat.card h46.W1 ≠ 0 := NeZero.ne _
    exact hne (by exact_mod_cast hcontra)
  · -- irreducible branch: non-real by odd order.
    exact caseB_irr_nonreal hyp hirr

/-- **Peterfalvi (6.8.2) case-(B) per-member `(5.4)` decomposition bundled with its (5.2.e)
cross-orthogonality and `τ₁`-agreement** (the coupled brick-1 datum for the norm-weighted member
family).

For a member `x` of a conjugation-closed coherent set `S₁ ⊆ S` and a fixed **break character**
`χ : Irr L` (the irreducible pair `{χ, χ̄}` being adjoined), produces the per-member `Dmem`
together with the two engine fields that must be *coupled* to it:

* `hortho` — the (5.2.e) cross-family orthogonality `R(x) ⊥ R(χ)`
  (`(Dmem).imageFamily.Orthogonal (dadeOrthonormalCharacterImageFamilyOfDiff … χ …)`), and
* `htau1` — the running-extension agreement `(Dmem).tau1 x = ν x` (`ν = hS₁coh.extension`).

This is the brick-1 dispatcher `caseB_member_psiDecomposition` enriched with the two
χ-dependent fields the norm-weighted engine `coherentDegreeSqNormBound_of_not_coherentW` demands.
Crucially the three outputs are produced in **one** transparent `by_cases` so they stay coupled:
proving `hortho`/`htau1` about the *opaque* black-box output of `caseB_member_psiDecomposition`
fails, because that output threads through the term-level transport `hcol ▸ …` (column branch),
which blocks the `rfl` shape of `htau1` and the imageSet identity `hortho` needs.

Dispatches on the `S`-member dichotomy `caseB_induce_column_or_irreducible`:

* **reducible certain-type column** `x = columnSum h46 χ₂` (`χ₂ ≠ 1`): `Dmem` is the
  reducible `R(μ_j)` decomposition `certainTypeMemberDecomposition`; `hortho` is the V-vanishing
  cross-orthogonality `certainTypeR_imageSet_orthogonal_dadeOfDiff` (needs only `χ`'s realness and
  `H^#`-support, *not* the member⊥break facts); `htau1` is `rfl` (`ofProjection`'s `τ₁` is `ν`);
* **irreducible** `x = Ind^L_H θ`: `Dmem` is `memberExtensionDecomposition`; `hortho` is the Dade
  difference-family orthogonality `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`, which
  consumes the member⊥break facts `hxχ`/`hxχbar`/`hxbarχ`/`hxbarχbar` (supplied by the caller
  from the break pair's orthogonality to `S₁`); `htau1` is `rfl`. -/
noncomputable def caseB_member_orthoDatum
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    {x : ClassFunction ↥L ℂ} (hxS₁ : x ∈ S₁)
    (hνZ : hS₁coh.extension x ∈ ZIrr G)
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hxχ : ClassFunction.inner x (χ : ClassFunction ↥L ℂ) = 0)
    (hxχbar : ClassFunction.inner x (χ : ClassFunction ↥L ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner x.conj (χ : ClassFunction ↥L ℂ) = 0)
    (hxbarχbar : ClassFunction.inner x.conj (χ : ClassFunction ↥L ℂ).conj = 0) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau x 0 //
      D.imageFamily.Orthogonal (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.dade χ hrealχ hdiffsuppχ) ∧
        D.tau1 x = hS₁coh.extension x } := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hxS : x ∈ hyp.S := hS₁sub hxS₁
  by_cases hcolumn : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x
  · -- reducible certain-type column branch
    set χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ := hcolumn.choose with hχ₂def
    have hχ₂ : χ₂ ≠ 1 := hcolumn.choose_spec.1
    have hcol : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x := hcolumn.choose_spec.2
    have hμ_S1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ S₁ := by rw [hcol]; exact hxS₁
    have hμbar_S1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj ∈ S₁ :=
      hS₁conj.conj_mem hμ_S1
    have hνZ' : hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) ∈ ZIrr G := by
      rw [hcol]; exact hνZ
    have hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
      exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂
        ((@inv_ne_one ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) _ χ₂).mpr hχ₂)
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
    -- the coupled datum at `columnSum χ₂`, transported to `x` along `hcol`.
    exact hcol ▸ (⟨OddOrder.Peterfalvi.S06.certainTypeMemberDecomposition h46 hχ₂
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
        (caseB_column_mapagree hyp h46 hχ₂) hS₁coh hμ_S1 hμbar_S1 hνZ'
        (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
          ⟨Submodule.sub_mem _ (Submodule.subset_span hμ_S1) (Submodule.subset_span hμbar_S1),
            hsupp⟩),
      certainTypeR_imageSet_orthogonal_dadeOfDiff hyp h46 hHK hχ₂
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm χ hrealχ hdiffsuppχ,
      rfl⟩ :
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) 0 //
        D.imageFamily.Orthogonal (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            hyp.dade χ hrealχ hdiffsuppχ) ∧
          D.tau1 (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
            = hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) })
  · -- irreducible branch
    have hirrx : IsIrreducibleCharacter x :=
      (caseB_S_member_column_or_irreducible hyp h46 hHK hxS).resolve_left hcolumn
    have hreal : ¬ ClassFunction.IsReal x := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_nonreal hyp (hxeq ▸ hirrx)
    have hdiffsupp : (x.conj - x).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_diff_support hyp θ
    have hχχbar : ClassFunction.inner x x.conj = 0 := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_inner hyp (hxeq ▸ hirrx)
    refine ⟨memberExtensionDecomposition hyp.dade hS₁coh ⟨x, hirrx⟩
      hreal hdiffsupp hxS₁ (hS₁conj.conj_mem hxS₁) hνZ hχχbar, ?_, rfl⟩
    -- `(Dmem).imageFamily = R(x)` (the Dade difference family), `⊥ R(χ)` by the (5.2.e) lemma.
    exact dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp.dade
      hreal hdiffsupp hrealχ hdiffsuppχ hxχ hxχbar hxbarχ hxbarχbar

/-- **(6.8.2) per-member `(5.4)` decomposition bundled with its (5.2.e) cross-orthogonality, for a
reducible certain-type COLUMN break.**

The column-break analogue of `caseB_member_orthoDatum`: the break being adjoined is a reducible
certain-type column `μ_b = columnSum χ₂b` (not an irreducible pair), so each member's image family
`R(x)` must be orthogonal to the column break's family `R(μ_b) = certainTypeR χ₂b`.  The member
`Dmem`/`htau1` are produced exactly as in the irreducible-break case (break-independent); only the
cross-orthogonality changes, dispatched on the member dichotomy:

* **column member** `x = columnSum χ₂x` — `certainTypeR(χ₂x) ⊥ certainTypeR(χ₂b)` by
  `certainTypeR_imageSet_orthogonal_certainTypeR` (column×column (5.2.e), 4a), whose disjointness
  `χ₂x ≠ χ₂b`, `χ₂x ≠ χ₂b⁻¹` is forced by `x ≠ μ_b`, `x ≠ μ̄_b`;
* **irreducible member** `x = Ind θ` — `dadeOfDiff(x) ⊥ certainTypeR(χ₂b)` by
  `dadeOfDiff_imageSet_orthogonal_certainTypeR` (irreducible×column, the conjugate-symmetry swap).

Unlike `caseB_member_orthoDatum`, neither branch needs the member⊥break inner products — the
column-break cross-orthogonality is structural (V-vanishing / grid disjointness). -/
noncomputable def caseB_member_orthoDatum_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    {x : ClassFunction ↥L ℂ} (hxS₁ : x ∈ S₁)
    (hνZ : hS₁coh.extension x ∈ ZIrr G)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hdegb : (∑ i, ((h46.columnFamily χ₂b).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂b⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (hxneq : x ≠ OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
    (hxneq' : x ≠ (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau x 0 //
      (∀ α ∈ D.imageFamily.imageSet,
          ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂b hdegb).imageSet,
            ClassFunction.inner α β = 0) ∧
        D.tau1 x = hS₁coh.extension x } := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hxS : x ∈ hyp.S := hS₁sub hxS₁
  by_cases hcolumn : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x
  · -- reducible certain-type column member branch
    set χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ := hcolumn.choose with hχ₂def
    have hχ₂ : χ₂ ≠ 1 := hcolumn.choose_spec.1
    have hcol : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x := hcolumn.choose_spec.2
    have hμ_S1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂ ∈ S₁ := by rw [hcol]; exact hxS₁
    have hμbar_S1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj ∈ S₁ :=
      hS₁conj.conj_mem hμ_S1
    have hνZ' : hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) ∈ ZIrr G := by
      rw [hcol]; exact hνZ
    have hsupp : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
      exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46 hχ₂
        ((@inv_ne_one ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) _ χ₂).mpr hχ₂)
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
    -- disjointness of the member column from the break column (and its inverse).
    have hne1 : χ₂ ≠ χ₂b := fun he => hxneq (by rw [← hcol, he])
    have hne2 : χ₂ ≠ χ₂b⁻¹ := fun he =>
      hxneq' (by rw [← hcol, OddOrder.Peterfalvi.S06.columnSum_conj_eq, he])
    exact hcol ▸ (⟨OddOrder.Peterfalvi.S06.certainTypeMemberDecomposition h46 hχ₂
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm
        (caseB_column_mapagree hyp h46 hχ₂) hS₁coh hμ_S1 hμbar_S1 hνZ'
        (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
          ⟨Submodule.sub_mem _ (Submodule.subset_span hμ_S1) (Submodule.subset_span hμbar_S1),
            hsupp⟩),
      OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46 hχ₂ hχ₂b
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm hdegb hne1 hne2,
      rfl⟩ :
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) 0 //
        (∀ α ∈ D.imageFamily.imageSet,
            ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂b hdegb).imageSet,
              ClassFunction.inner α β = 0) ∧
          D.tau1 (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
            = hS₁coh.extension (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) })
  · -- irreducible member branch
    have hirrx : IsIrreducibleCharacter x :=
      (caseB_S_member_column_or_irreducible hyp h46 hHK hxS).resolve_left hcolumn
    have hreal : ¬ ClassFunction.IsReal x := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_nonreal hyp (hxeq ▸ hirrx)
    have hdiffsupp : (x.conj - x).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_diff_support hyp θ
    have hχχbar : ClassFunction.inner x x.conj = 0 := by
      have h := hxS; rw [hyp.S_eq, Set.mem_ofPred_eq] at h
      obtain ⟨θ, hθne, hxeq⟩ := h
      rw [hxeq]; exact caseB_irr_conj_inner hyp (hxeq ▸ hirrx)
    refine ⟨memberExtensionDecomposition hyp.dade hS₁coh ⟨x, hirrx⟩
      hreal hdiffsupp hxS₁ (hS₁conj.conj_mem hxS₁) hνZ hχχbar, ?_, rfl⟩
    -- `(Dmem).imageFamily = R(x)` (Dade difference family) `⊥ R(μ_b) = certainTypeR χ₂b`.
    exact dadeOfDiff_imageSet_orthogonal_certainTypeR hyp h46 hHK hχ₂b hdegb ⟨x, hirrx⟩
      hreal hdiffsupp

/-- **Peterfalvi (6.8.2) case-(B): distinct `S`-members are pairwise orthogonal.**

For distinct members `x ≠ y` of `S` (any two, not just the `X(W₂) ∪ Y` seed), `⟨x, y⟩ = 0`.  This
is the off-diagonal of the weighted Gram matrix the norm-weighted (5.6) engine consumes, for an
arbitrary conjugation-closed coherent `S₁ ⊆ S` (the break pair yields `S₁ ⊋ X(W₂) ∪ Y`).  The
genuinely new structural fact case (B) needs, since `S`-members are no longer all irreducible: `S`
contains the reducible certain-type columns `columnSum h46 χ₂`.

Each `S`-member splits, by `caseB_S_member_column_or_irreducible`, into a nontrivial column or an
irreducible:

* **column vs column** — distinct columns (`χ₂ ≠ χ₂'`, forced by `x ≠ y`) are orthogonal by
  `inner_columnSum_cross_eq_zero` (Peterfalvi (4.1) grid cross-orthogonality);
* **column vs irreducible** / **irreducible vs column** — a column and an irreducible `Ind^L_H θ`
  are orthogonal by `caseB_inner_irr_columnSum_eq_zero` (the degree-`mod |W₁|` argument), one order
  via conjugate symmetry;
* **irreducible vs irreducible** — distinct irreducibles are orthogonal
  (`irreducibleCharacter_inner_eq_ite`). -/
theorem caseB_S_pairwise_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)] :
    ∀ x ∈ hyp.S, ∀ y ∈ hyp.S, x ≠ y → ClassFunction.inner x y = 0 := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  -- helper: an irreducible `S`-member is orthogonal to every certain-type column.
  have hirr_col : ∀ z, IsIrreducibleCharacter z → z ∈ hyp.S →
      ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ,
      ClassFunction.inner z (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = 0 := by
    intro z hzirr hzS χ₂
    rw [hyp.S_eq, Set.mem_ofPred_eq] at hzS
    obtain ⟨θ, hθne, rfl⟩ := hzS
    exact caseB_inner_irr_columnSum_eq_zero hyp h46 hW1 hzirr χ₂
  intro x hxS y hyS hxy
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK hxS with ⟨χ₂, hχ₂, hcolx⟩ | hirrx
  · rcases caseB_S_member_column_or_irreducible hyp h46 hHK hyS with ⟨χ₂', hχ₂', hcoly⟩ | hirry
    · -- column vs column
      have hne : χ₂ ≠ χ₂' := fun h => hxy (by subst h; exact hcolx.symm.trans hcoly)
      exact hcolx ▸ hcoly ▸ inner_columnSum_cross_eq_zero h46 hne
    · -- column vs irreducible (conjugate symmetry of irreducible vs column)
      refine hcolx ▸ ?_
      rw [inner_conj_symm y (OddOrder.Peterfalvi.S06.columnSum h46 χ₂),
        hirr_col y hirry hyS χ₂, star_zero]
  · rcases caseB_S_member_column_or_irreducible hyp h46 hHK hyS with ⟨χ₂', hχ₂', hcoly⟩ | hirry
    · -- irreducible vs column
      exact hcoly ▸ hirr_col x hirrx hxS χ₂'
    · -- irreducible vs irreducible
      have h := irreducibleCharacter_inner_eq_ite
        (⟨x, hirrx⟩ : IrreducibleCharacter ↥L) ⟨y, hirry⟩
      rwa [if_neg (fun he => hxy (congrArg Subtype.val he))] at h

/-- **Peterfalvi (6.8.2) case-(B) norm-weighted member-family enumerator** (brick 2): the
ψ-independent data of the norm-weighted (5.6) member family for an arbitrary finite `S₁ ⊆ S`.

Enumerates `S₁` (any finite subset of `S`, by `exists_finEnum_general` — *not*
`exists_finEnum_irreducible`, since case (B) members include the reducible certain-type columns) as
an injective `Fin k`-family `χmem : Fin k → ClassFunction ↥L ℂ`, together with:

* the per-member squared norms `mc j = (⟨χmem j, χmem j⟩).re`, all positive (`|W₁|` for the columns,
  `1` for the irreducibles, by the `S`-member dichotomy `caseB_S_member_column_or_irreducible`);
* the **weighted Gram identity** `⟨χmem i, χmem j⟩ = if i = j then (mc i : ℂ) else 0` — diagonal the
  real squared norm (`inner_self_eq_realCast`), off-diagonal `0` by `caseB_S_pairwise_orthogonal`.

This is exactly the `χmem`/`mc`/`hmempos`/`hmemortho` block the engine
`coherentDegreeSqNormBound_of_not_coherentW` consumes; the χ-dependent per-member data
(`Dmem`/`hortho_mem`/`htau1Dmem`, supplied by `caseB_member_orthoDatum`) and the degree data are
layered on in the (6.8.3) bound (brick 3).  Taking `S₁ = X(W₂) ∪ Y` recovers the seed enumerator. -/
theorem exists_sMemberOrthogonalFamilyW
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S) (hS₁fin : S₁.Finite) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, χmem j ∈ S₁) ∧
      (∀ j, 0 < mc j) ∧
      (∀ i j, ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0) := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  obtain ⟨k, χmem, hinj, hrange⟩ := exists_finEnum_general hS₁fin
  have hmemS1 : ∀ j, χmem j ∈ S₁ := fun j => hrange ▸ Set.mem_range_self j
  refine ⟨k, χmem, fun j => (ClassFunction.inner (χmem j) (χmem j)).re,
    hinj, hrange, hmemS1, ?_, ?_⟩
  · -- `mc j > 0`: column members have `‖μ_j‖² = |W₁|`, irreducibles have `‖χ‖² = 1`.
    intro j
    change (0 : ℝ) < (ClassFunction.inner (χmem j) (χmem j)).re
    rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hS₁sub (hmemS1 j)) with
      ⟨χ₂, hχ₂, hcol⟩ | hirr
    · have hval := OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner h46 χ₂ χ₂
      rw [if_pos rfl] at hval
      simp only [← OddOrder.Peterfalvi.S06.columnSum_def] at hval
      rw [hcol] at hval
      rw [hval, Complex.natCast_re]
      exact_mod_cast Nat.card_pos
    · have hval : ClassFunction.inner (χmem j) (χmem j) = 1 := by
        have h := irreducibleCharacter_inner_eq_ite
          (⟨χmem j, hirr⟩ : IrreducibleCharacter ↥L) ⟨χmem j, hirr⟩
        rwa [if_pos rfl] at h
      rw [hval]; norm_num
  · -- weighted Gram: diagonal the real squared norm, off-diagonal `0`.
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      change ClassFunction.inner (χmem i) (χmem i)
        = (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ)
      rw [inner_self_eq_realCast (χmem i), Complex.ofReal_re]
    · rw [if_neg hij]
      exact caseB_S_pairwise_orthogonal hyp h46 hHK hW1
        (χmem i) (hS₁sub (hmemS1 i)) (χmem j) (hS₁sub (hmemS1 j)) (fun h => hij (hinj h))

/-- **Peterfalvi (6.8.3) case-(B) break-character fields** (the case-(B) analogue of
`sBreakPair_fields`).

For an irreducible `S`-member `ψ` whose pair `{ψ, ψ̄}` is disjoint from the coherent seed
`S₁ = X(W₂) ∪ Y`, packages the eight break-character facts the norm-weighted (5.6) engine
`coherentDegreeSqNormBound_of_not_coherentW` demands of its adjoined irreducible: `ψ` is non-real
(`caseB_irr_nonreal`), the self/cross inner products are the irreducible Kronecker values
(`irreducibleCharacter_inner_eq_ite`, `caseB_irr_conj_inner`), the conjugate difference is
`H^#`-supported (`caseB_irr_conj_diff_support`), and `ψ`, `ψ̄` are orthogonal to every member of
`S₁`.  The last two — `ψ ⊥ S₁` and `ψ̄ ⊥ S₁` — are the case-(B) novelty: `S₁` is no longer all
irreducible, so a member may be a reducible certain-type column `columnSum h46 χ₂`, against which
orthogonality is the degree-`mod |W₁|` argument `caseB_inner_irr_columnSum_eq_zero` rather than the
irreducible Kronecker delta. -/
theorem caseB_breakChar_fields
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁) :
    ¬ ClassFunction.IsReal ψ ∧
      ClassFunction.inner ψ ψ = 1 ∧ ClassFunction.inner ψ.conj ψ.conj = 1 ∧
      ClassFunction.inner ψ.conj ψ = 0 ∧ ClassFunction.inner ψ ψ.conj = 0 ∧
      ((ψ.conj - ψ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner ψ.conj χ = 0) := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  -- `ψ = Ind^L_H θ` for a (nontrivial) source `θ` (membership in `S`).
  have hψS' := hψS
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hψS'
  obtain ⟨θ, -, hψeq⟩ := hψS'
  have hψirr' : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) :=
    hψeq ▸ hψirr
  -- intrinsic facts of the pair `{ψ, ψ̄}`.
  have hreal : ¬ ClassFunction.IsReal ψ := by rw [hψeq]; exact caseB_irr_nonreal hyp hψirr'
  have hψψ : ClassFunction.inner ψ ψ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥L) ⟨ψ, hψirr⟩
    rwa [if_pos rfl] at h
  have hψbarψbar : ClassFunction.inner ψ.conj ψ.conj = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ.conj, hψirr.conj⟩ : IrreducibleCharacter ↥L) ⟨ψ.conj, hψirr.conj⟩
    rwa [if_pos rfl] at h
  have hψψbar : ClassFunction.inner ψ ψ.conj = 0 := by
    rw [hψeq]; exact caseB_irr_conj_inner hyp hψirr'
  have hψbarψ : ClassFunction.inner ψ.conj ψ = 0 := by
    rw [inner_conj_symm ψ ψ.conj, hψψbar, star_zero]
  have hdiffsupp : (ψ.conj - ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [hψeq]; exact caseB_irr_conj_diff_support hyp θ
  -- `φ ⊥ S₁` for an `S`-member `φ ∉ S₁`: distinct `S`-members are orthogonal.
  have hortho : ∀ φ, φ ∈ hyp.S → φ ∉ S₁ → ∀ χ ∈ S₁, ClassFunction.inner φ χ = 0 := by
    intro φ hφS hφnotS1 χ hχ
    exact caseB_S_pairwise_orthogonal hyp h46 hHK hW1 φ hφS χ (hS₁sub hχ)
      (fun h => hφnotS1 (by rw [h]; exact hχ))
  exact ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsupp,
    hortho ψ hψS hψnotS1,
    hortho ψ.conj (hyp.S_closedUnderConjugate.conj_mem hψS) hψcnotS1⟩

/-- **(6.8.3) case-(B) break-character fields for a reducible certain-type COLUMN break.**

The column analogue of `caseB_breakChar_fields`: for a certain-type column `μ_b = columnSum χ₂b`
(`χ₂b ≠ 1`) whose pair `{μ_b, μ̄_b}` is disjoint from the coherent set `S₁`, the eight
break-character facts the norm-weighted (5.6) engine consumes — with the self/cross norms now
`‖μ_b‖² = ‖μ̄_b‖² = w₁ ≠ 0` (not `= 1`, since `μ_b` is reducible), supplied to the reducible-break
contrapositive `coherentDegreeSqNormBound_of_not_coherentW_k`.  All from the certain-type column
machinery: `columnFamily_mu_sum_inner` (grid norms, `⟨μ_b, μ_b⟩ = w₁`, `⟨μ_b, μ̄_b⟩ = 0` since
`χ₂b ≠ χ₂b⁻¹`), `columnSum_conj_eq` (`μ̄_b = columnSum χ₂b⁻¹`), `column_inv_ne_self`,
`columnDiff_support_subset` (support), and `caseB_S_pairwise_orthogonal` (`μ_b, μ̄_b ∈ S` via
`columnSum_mem_S`, distinct from `S₁`-members). -/
theorem caseB_breakChar_fields_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hψnotS1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∉ S₁)
    (hψcnotS1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∉ S₁) :
    ¬ ClassFunction.IsReal (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) ∧
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) ≠ 0 ∧
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ≠ 0 ∧
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) = 0 ∧
      ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
          (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj = 0 ∧
      (((OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
          - OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧
      (∀ χ ∈ S₁, ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) χ = 0) ∧
      (∀ χ ∈ S₁, ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj χ = 0) := by
  classical
  have hw1ne : (Nat.card h46.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hμS : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∈ hyp.S :=
    hyp.columnSum_mem_S h46 hHK hχ₂b
  have hμbarS : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∈ hyp.S := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    exact hyp.columnSum_mem_S h46 hHK
      ((@inv_ne_one ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) _ χ₂b).mpr hχ₂b)
  -- self/cross norms via `columnFamily_mu_sum_inner` (`= if χ₂=χ₂' then w₁ else 0`).
  have hψψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) ≠ 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]
    exact hw1ne
  have hψbarψbar : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ≠ 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]
    exact hw1ne
  have hψbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂b)]
  have hψψbar : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂b).symm]
  have hreal : ¬ ClassFunction.IsReal (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) := by
    intro hr
    have heq : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
      = OddOrder.Peterfalvi.S06.columnSum h46 χ₂b := hr
    rw [heq] at hψψbar
    exact hψψ hψψbar
  have hdiffsupp : ((OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
      - OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq]
    exact OddOrder.Peterfalvi.S06.columnDiff_support_subset h46
      ((@inv_ne_one ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) _ χ₂b).mpr hχ₂b) hχ₂b
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂b)
  have hortho : ∀ φ, φ ∈ hyp.S → φ ∉ S₁ → ∀ χ ∈ S₁, ClassFunction.inner φ χ = 0 :=
    fun φ hφS hφnotS1 χ hχ =>
      caseB_S_pairwise_orthogonal hyp h46 hHK hW1 φ hφS χ (hS₁sub hχ)
        (fun he => hφnotS1 (by rw [he]; exact hχ))
  exact ⟨hreal, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsupp,
    hortho _ hμS hψnotS1, hortho _ hμbarS hψcnotS1⟩

/-- **Peterfalvi (6.8.3) case-(B) norm-weighted member-family degree-square bound** (brick 3, the
weighted analogue of `sMember_degreeSumBound_of_not_coherent`).

For an arbitrary conjugation-closed coherent finite `S₁ ⊆ S` with a `Y`-anchor `η ∈ S₁` (degree
`|W₁|`, irreducible hence weight `‖η‖² = 1`) and a break character `ψ ∈ S` whose pair `{ψ, ψ̄}` is
disjoint from `S₁` and *cannot* be coherently adjoined, the norm-weighted degree-ratio sum is
bounded by twice the degree ratio: `∑ⱼ (degⱼ)² / mcⱼ ≤ 2·a`, where `degⱼ = χⱼ(1)/η(1)`,
`mcⱼ = ‖χⱼ‖²` and `a = ψ(1)/η(1)`.  (`S₁ = X(W₂) ∪ Y` is the seed instance; the break pair yields
a larger `S₁`.)

All member-family fields are discharged from the landed case-(B) pieces: the ψ-independent
enumerator (`exists_sMemberOrthogonalFamilyW`, brick 2), the coupled per-member decomposition data
(`caseB_member_orthoDatum`), the degree data (`sMember_charValue_one_eq_mul_anchor`), the break
character fields (`caseB_breakChar_fields`), the scaled-difference support + Dade image
(`sMember_scaledDiffSupport_of_charValue_eq`, `scaledDiff_dadeImage_mem_ZIrr`), and the abstract S07
generation bridges.  The bound is fed by the norm-weighted (5.6) engine
`coherentDegreeSqNormBound_of_not_coherentW`.  This is the (6.2) step
"`2ψ(1)|L:K| ≥ ∑_{χ∈S₁} χ(1)²/‖χ‖²`" in normalized integer form, for the reducible-member
case (B). -/
theorem sMember_degreeSqNormBound_of_not_coherent
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, 0 < mc j) ∧
      (∀ j, ClassFunction.inner (χmem j) (χmem j) = (mc j : ℂ)) ∧
      (∀ j, χmem j 1 = (deg j : ℂ) * η 1) ∧
      ψ 1 = (a : ℂ) * η 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 / mc j ≤ 2 * (a : ℝ) := by
  classical
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  -- (1) the ψ-independent member family (brick 2).
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1set, hmcpos, hmemortho⟩ :=
    exists_sMemberOrthogonalFamilyW hyp h46 hHK hW1 hS₁sub hS₁fin
  have hmemS : ∀ j, χmem j ∈ hyp.S := fun j => hS₁sub (hmemS1set j)
  -- (2) the anchor index `i₁` (the `Y`-anchor `η` lies in `range χmem = S₁`).
  obtain ⟨i₁, hi₁eq⟩ : η ∈ Set.range χmem := by rw [hrange]; exact hηS₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hηY
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := hyp.Yset_apply_one hηY
  have hanchordeg : χmem i₁ 1 = (Nat.card hyp.W1 : ℂ) := by rw [hi₁eq]; exact hηdeg
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- (3) the degree data against the anchor `χmem i₁`.
  choose deg hdeg_pos hdeg_eq using fun j =>
    hyp.sMember_charValue_one_eq_mul_anchor (hmemS j) hanchordeg
  have hdeg_i₁ : deg i₁ = 1 := by
    have h := hdeg_eq i₁; rw [hanchordeg] at h
    have hd1 : (deg i₁ : ℂ) = 1 := mul_right_cancel₀ hW1ne (by rw [one_mul]; exact h.symm)
    exact_mod_cast hd1
  have hmemdegdiffsupp : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      ((χmem i) - deg i • (χmem i₁)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun i _ => hyp.sMember_scaledDiffSupport_of_charValue_eq (hmemS i) (hmemS i₁) (hdeg_eq i)
  -- (4) break-character fields and the ψ degree ratio.
  obtain ⟨hrealψ, hψψ, hψbarψbar, hψbarψ, hψψbar, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    caseB_breakChar_fields hyp h46 hHK hW1 hS₁sub hψS hψirr hψnotS1 hψcnotS1
  obtain ⟨a, _ha_pos, hψratio⟩ := hyp.sMember_charValue_one_eq_mul_anchor hψS hanchordeg
  have hdiffasuppψ : (ψ - a • (χmem i₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq hψS (hmemS i₁) hψratio
  have hanchorIrr : IsIrreducibleCharacter (χmem i₁) := by rw [hi₁eq]; exact hηirr
  have htau1ψ : hyp.tau (ψ - a • (χmem i₁)) ∈ ZIrr G :=
    hyp.scaledDiff_dadeImage_mem_ZIrr (χ := ⟨ψ, hψirr⟩) (χ₁ := ⟨χmem i₁, hanchorIrr⟩) hdiffasuppψ
  -- (5) the generation bridges (weighting-independent).
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧
      χmem j = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
    hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : ψ.conj 1 = ψ 1 := by
    rw [ClassFunction.conj_apply]
    obtain ⟨n, -, hn1, -⟩ := hψirr.exists_natDegree_charValue_one_dvd_card
    rw [hn1, star_natCast]
  have hchi1_ne : (χmem i₁) 1 ≠ 0 := by rw [hanchordeg]; exact hW1ne
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := ψ) (chibar := ψ.conj) (chi1 := (χmem i₁)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  -- (6) the coupled per-member decomposition data (`Dmem`/`hortho`/`htau1`), supplied per member.
  have datum : ∀ i : Fin k,
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau (χmem i) 0 //
        D.imageFamily.Orthogonal (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            hyp.dade ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ) ∧
          D.tau1 (χmem i) = hS₁coh.extension (χmem i) } := fun i => by
    refine caseB_member_orthoDatum hyp h46 hHK hS₁sub hS₁coh hS₁conj (hmemS1set i)
      (hS₁coh.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1set i)))
      ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ ?_ ?_ ?_ ?_
    · rw [inner_conj_symm ψ (χmem i), hψ_S1 (χmem i) (hmemS1set i), star_zero]
    · rw [inner_conj_symm ψ.conj (χmem i), hψbar_S1 (χmem i) (hmemS1set i), star_zero]
    · rw [inner_conj_symm ψ ((χmem i).conj), hψ_S1 ((χmem i).conj) (hS₁conj (hmemS1set i)),
        star_zero]
    · rw [inner_conj_symm ψ.conj ((χmem i).conj),
        hψbar_S1 ((χmem i).conj) (hS₁conj (hmemS1set i)), star_zero]
  -- (7) feed everything to the norm-weighted (5.6) engine.
  have hbound := coherentDegreeSqNormBound_of_not_coherentW hyp.dade hS₁coh
    ⟨ψ, hψirr⟩ hrealψ hdiffsuppψ hψψ hψbarψbar hψψbar hψbarψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁) hmemdegdiffsupp
    (fun i _ => hmemS1set i) mc (fun i _ => hmcpos i)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    (fun i _ => (datum i).1) (fun i _ => (datum i).2.1) (fun i _ => (datum i).2.2)
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  -- (8) package the output, converting the anchor `χmem i₁` to `η`.
  refine ⟨k, χmem, mc, deg, a, hinj, hrange, hmcpos,
    fun j => by have h := hmemortho j j; rwa [if_pos rfl] at h,
    fun j => by rw [hdeg_eq j, hi₁eq], by rw [hψratio, hi₁eq], hbound⟩

/-- **(6.8.3) case-(B) norm-weighted member-family degree bound, reducible COLUMN break.**

The column-break analogue of `sMember_degreeSqNormBound_of_not_coherent`: the adjoined break is a
reducible certain-type column `μ_b = columnSum χ₂b` (not an irreducible pair).  Same conclusion
`∑ⱼ degⱼ²/mcⱼ ≤ 2a`, via the reducible-break engine: break fields from
`caseB_breakChar_fields_columnBreak` (4b), per-member datum from
`caseB_member_orthoDatum_columnBreak`
(4c), break decomposition `columnDecompositionTau` (over `hyp.tau`, `tau1 = hyp.tau`, image family
`columnRFamilyTau` with `imageSet = certainTypeR χ₂b` so the 4c raw orthogonality is definitionally
`.Orthogonal`), and the bound from the reducible contrapositive
`coherentDegreeSqNormBound_of_not_coherentW_k`. -/
theorem sMember_degreeSqNormBound_of_not_coherent_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hψnotS1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∉ S₁)
    (hψcnotS1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {OddOrder.Peterfalvi.S06.columnSum h46 χ₂b,
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ) (deg : Fin k → ℕ) (a : ℕ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, 0 < mc j) ∧
      (∀ j, ClassFunction.inner (χmem j) (χmem j) = (mc j : ℂ)) ∧
      (∀ j, χmem j 1 = (deg j : ℂ) * η 1) ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1 = (a : ℂ) * η 1 ∧
      ∑ j : Fin k, ((deg j : ℝ)) ^ 2 / mc j ≤ 2 * (a : ℝ) := by
  classical
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  -- (1) the ψ-independent member family (brick 2) — identical to the irreducible-break case.
  obtain ⟨k, χmem, mc, hinj, hrange, hmemS1set, hmcpos, hmemortho⟩ :=
    exists_sMemberOrthogonalFamilyW hyp h46 hHK hW1 hS₁sub hS₁fin
  have hmemS : ∀ j, χmem j ∈ hyp.S := fun j => hS₁sub (hmemS1set j)
  obtain ⟨i₁, hi₁eq⟩ : η ∈ Set.range χmem := by rw [hrange]; exact hηS₁
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hηY
  have hηdeg : η 1 = (Nat.card hyp.W1 : ℂ) := hyp.Yset_apply_one hηY
  have hanchordeg : χmem i₁ 1 = (Nat.card hyp.W1 : ℂ) := by rw [hi₁eq]; exact hηdeg
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  choose deg hdeg_pos hdeg_eq using fun j =>
    hyp.sMember_charValue_one_eq_mul_anchor (hmemS j) hanchordeg
  have hdeg_i₁ : deg i₁ = 1 := by
    have h := hdeg_eq i₁; rw [hanchordeg] at h
    have hd1 : (deg i₁ : ℂ) = 1 := mul_right_cancel₀ hW1ne (by rw [one_mul]; exact h.symm)
    exact_mod_cast hd1
  have hmemdegdiffsupp : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      ((χmem i) - deg i • (χmem i₁)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun i _ => hyp.sMember_scaledDiffSupport_of_charValue_eq (hmemS i) (hmemS i₁) (hdeg_eq i)
  have hanchorIrr : IsIrreducibleCharacter (χmem i₁) := by rw [hi₁eq]; exact hηirr
  -- (4) column break fields (4b) and the degree ratio.
  obtain ⟨_hrealψ, hψψne, hψbarψbarne, hψbarψ, hψψbar, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    caseB_breakChar_fields_columnBreak hyp h46 hHK hW1 hS₁sub hχ₂b hψnotS1 hψcnotS1
  have hψS : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∈ hyp.S :=
    hyp.columnSum_mem_S h46 hHK hχ₂b
  obtain ⟨a, _ha_pos, hψratio⟩ := hyp.sMember_charValue_one_eq_mul_anchor hψS hanchordeg
  have hdiffasuppψ : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b - a • (χmem i₁)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_scaledDiffSupport_of_charValue_eq hψS (hmemS i₁) hψratio
  -- the column virtual `μ_b ∈ ℤ[Irr L]` (sum of irreducibles), and the `H^#`-supported Dade image.
  have hψZ : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∈ ZIrr ↥L := by
    rw [OddOrder.Peterfalvi.S06.columnSum_def]
    exact Submodule.sum_mem _ (fun i _ => ((h46.columnFamily χ₂b).mu i).mem_ZIrr)
  have htau1ψ : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b - a • (χmem i₁)) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported hyp.dade
      hdiffasuppψ
      (Submodule.sub_mem _ hψZ (nsmul_mem hanchorIrr.mem_ZIrr a))
  -- (5) generation bridges; `hbar1` from the column's real degree.
  have hcover : ∀ x ∈ S₁, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen := OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
    (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
    hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj 1
      = OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq, OddOrder.Peterfalvi.S06.columnSum_apply_one,
      OddOrder.Peterfalvi.S06.columnSum_apply_one]
    exact OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂b
  have hchi1_ne : (χmem i₁) 1 ≠ 0 := by rw [hanchordeg]; exact hW1ne
  have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
  have hgen := OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
    (χ := OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
    (chibar := (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj) (chi1 := (χmem i₁)) (a := a)
    hSgen hψratio hbar1 hchi1_ne h1A
  -- (6) per-member datum against the column break family (4c, raw `imageSet`-orthogonality).
  have hdegb : (∑ i, ((h46.columnFamily χ₂b).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂b⁻¹).mu i : ClassFunction ↥L ℂ) 1) :=
    (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂b).symm
  have datum : ∀ i : Fin k,
      { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau (χmem i) 0 //
        (∀ α ∈ D.imageFamily.imageSet,
            ∀ β ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂b hdegb).imageSet,
              ClassFunction.inner α β = 0) ∧
          D.tau1 (χmem i) = hS₁coh.extension (χmem i) } := fun i =>
    caseB_member_orthoDatum_columnBreak hyp h46 hHK hS₁sub hS₁coh hS₁conj (hmemS1set i)
      (hS₁coh.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1set i))) hχ₂b hdegb
      (fun he => hψnotS1 (by rw [← he]; exact hmemS1set i))
      (fun he => hψcnotS1 (by rw [← he]; exact hmemS1set i))
  -- the break decomposition over `hyp.tau` (column branch of `caseB_constituentDecomposition`).
  have hSdiffDa : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂b
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj,
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂b - a • (χmem i₁)} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show OddOrder.Peterfalvi.S06.columnSum h46 χ₂b
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
          = -((OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
            - OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) from by abel, ClassFunction.support_neg]
      exact hdiffsuppψ
    · exact hdiffasuppψ
  have hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b)
      (a • (χmem i₁) : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), OddOrder.RepresentationTheory.inner_smul_right,
      hψ_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  have hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj
      (a • (χmem i₁) : ClassFunction ↥L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), OddOrder.RepresentationTheory.inner_smul_right,
      hψbar_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  let Da := columnDecompositionTau hyp h46 hχ₂b hdegb (η₁ := χmem i₁) (a := a)
    (caseB_column_mapagree hyp h46 hχ₂b) hSdiffDa htau1ψ hχψ hχbarψ
  -- (7) feed everything to the reducible-break norm-weighted (5.6) contrapositive.
  have hbound := coherentDegreeSqNormBound_of_not_coherentW_k hyp.dade hS₁coh
    (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b) hdiffsuppψ hψψne hψbarψbarne hψψbar hψbarψ
    hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁) hmemdegdiffsupp
    (fun i _ => hmemS1set i) mc (fun i _ => hmcpos i)
    (fun i _ j _ => by rw [hmemortho i j]; rcases eq_or_ne i j with h | h <;> simp [h])
    (fun i _ => (datum i).1) Da rfl (fun i _ => (datum i).2.1) (fun i _ => (datum i).2.2)
    hdiffasuppψ htau1ψ hdeg_i₁ hSgen hgen hnc
  -- (8) package the output, converting the anchor `χmem i₁` to `η`.
  refine ⟨k, χmem, mc, deg, a, hinj, hrange, hmcpos,
    fun j => by have h := hmemortho j j; rwa [if_pos rfl] at h,
    fun j => by rw [hdeg_eq j, hi₁eq], by rw [hψratio, hi₁eq], hbound⟩

/-- **Peterfalvi (6.8.3) case-(B) norm-weighted member-family degree-square bound** (real form).

The degree-ratio bound `sMember_degreeSqNormBound_of_not_coherent` (`∑ⱼ (degⱼ)²/mcⱼ ≤ 2a`), rescaled
by the anchor degree `η(1) = |W₁|`, gives the norm-weighted character-degree-square sum over the
enumerated `S₁ = X(W₂) ∪ Y` family: `∑ⱼ (χⱼ(1))²/‖χⱼ‖² ≤ 2·ψ(1)·η(1)` (real parts), since
`χⱼ(1) = degⱼ·η(1)` and `ψ(1) = a·η(1)`.  This is the case-(B) (6.2) bound
`∑_{χ∈S₁} χ(1)²/‖χ‖² ≤ 2ψ(1)η(1)` in the form ready to be compared, via `X(W₂) ⊆ S₁` and the
norm-weighted counting `sum_div_normSq_induce_kernelFilter_eq`, with the `X` degree-sum identity. -/
theorem sMember_degreeSqNormReBound_of_not_coherent
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {ψ : ClassFunction ↥L ℂ} (hψS : ψ ∈ hyp.S) (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {ψ, ψ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, χmem j ∈ S₁) ∧
      (∀ j, 0 < mc j) ∧
      (∀ j, ClassFunction.inner (χmem j) (χmem j) = (mc j : ℂ)) ∧
      ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j ≤ 2 * (ψ 1).re * (η 1).re := by
  obtain ⟨k, χmem, mc, deg, a, hinj, hrange, hmcpos, hmcnorm, hdeg_eq, hψ_eq, hbound⟩ :=
    sMember_degreeSqNormBound_of_not_coherent hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin hS₁coh hηY hηS₁
      hψS hψirr hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, χmem j ∈ S₁ := fun j => hrange ▸ Set.mem_range_self j
  refine ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, ?_⟩
  -- real parts of the degree relations
  have hdegre : ∀ j, (χmem j 1).re = (deg j : ℝ) * (η 1).re := by
    intro j
    rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (ψ 1).re = (a : ℝ) * (η 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  calc ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j
      = ∑ j : Fin k, ((deg j : ℝ) * (η 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (η 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 / mc j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (η 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * ((a : ℝ) * (η 1).re) * (η 1).re := by ring
    _ = 2 * (ψ 1).re * (η 1).re := by rw [hψre]

/-- **(6.8.3) case-(B) norm-weighted member-family degree bound (real form), reducible COLUMN
break.**  The real-part repackaging of `sMember_degreeSqNormBound_of_not_coherent_columnBreak`,
mirroring `sMember_degreeSqNormReBound_of_not_coherent` for the column break
`μ_b = columnSum χ₂b`. -/
theorem sMember_degreeSqNormReBound_of_not_coherent_columnBreak
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)} (hS₁sub : S₁ ⊆ hyp.S)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁) (hS₁fin : S₁.Finite)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η : ClassFunction ↥L ℂ} (hηY : η ∈ hyp.Yset) (hηS₁ : η ∈ S₁)
    {χ₂b : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂b : χ₂b ≠ 1)
    (hψnotS1 : OddOrder.Peterfalvi.S06.columnSum h46 χ₂b ∉ S₁)
    (hψcnotS1 : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj ∉ S₁)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (S₁ ∪ {OddOrder.Peterfalvi.S06.columnSum h46 χ₂b,
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    ∃ (k : ℕ) (χmem : Fin k → ClassFunction ↥L ℂ) (mc : Fin k → ℝ),
      Function.Injective χmem ∧
      Set.range χmem = S₁ ∧
      (∀ j, χmem j ∈ S₁) ∧
      (∀ j, 0 < mc j) ∧
      (∀ j, ClassFunction.inner (χmem j) (χmem j) = (mc j : ℂ)) ∧
      ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j
        ≤ 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := by
  obtain ⟨k, χmem, mc, deg, a, hinj, hrange, hmcpos, hmcnorm, hdeg_eq, hψ_eq, hbound⟩ :=
    sMember_degreeSqNormBound_of_not_coherent_columnBreak hyp h46 hHK hW1 hS₁sub hS₁conj hS₁fin
      hS₁coh hηY hηS₁ hχ₂b hψnotS1 hψcnotS1 hnc
  have hmemS1 : ∀ j, χmem j ∈ S₁ := fun j => hrange ▸ Set.mem_range_self j
  refine ⟨k, χmem, mc, hinj, hrange, hmemS1, hmcpos, hmcnorm, ?_⟩
  have hdegre : ∀ j, (χmem j 1).re = (deg j : ℝ) * (η 1).re := by
    intro j
    rw [hdeg_eq j, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  have hψre : (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re = (a : ℝ) * (η 1).re := by
    rw [hψ_eq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  calc ∑ j : Fin k, ((χmem j 1).re) ^ 2 / mc j
      = ∑ j : Fin k, ((deg j : ℝ) * (η 1).re) ^ 2 / mc j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hdegre j]
    _ = (η 1).re ^ 2 * ∑ j : Fin k, (deg j : ℝ) ^ 2 / mc j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
    _ ≤ (η 1).re ^ 2 * (2 * (a : ℝ)) := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * ((a : ℝ) * (η 1).re) * (η 1).re := by ring
    _ = 2 * (OddOrder.Peterfalvi.S06.columnSum h46 χ₂b 1).re * (η 1).re := by rw [hψre]

end OddOrder.Peterfalvi.S08


