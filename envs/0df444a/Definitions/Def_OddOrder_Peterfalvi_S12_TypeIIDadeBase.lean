-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIDadeBase
-- name    : OddOrder_Peterfalvi_S12_TypeIIDadeBase
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:03:48.581325+00:00
-- url     : https://prove2.me/theorems/83b49f59-9a67-4bf3-8bb2-b1d89f6d18a1
-- title:
--   Peterfalvi (8.16): the $S$-side Dade base for a type II maximal subgroup
-- statement:
--   Formalizes the $S$-side Dade base of Peterfalvi (8.16), together with (4.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, p. 48), for a type II maximal subgroup.
--
--   Main declarations: `typeIIDadeHypothesis` (Peterfalvi (8.16) ⇒ Hypothesis (2.2) for `(A(S), S)`, Type II); `typeII_sSet_member_support_subset` (Peterfalvi (4.7)/(8.15), §9-family induced support, type-II instance).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeIIDadeBase.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeIIDadeBase.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Section9Counts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometryBasic
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

section DadeBase

open OddOrder.BG.Ch3.S10

/-- **Peterfalvi (8.16), TI part, for the honest type-II `A(S)`**: for a Type-II maximal
subgroup `S`, the (8.10) support `A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#` is a TI-subset of `G` with
normalizer bound `S`.

The proof splits a conjugation `g·a·g⁻¹ = b` with `a, b ∈ A(S)` by `S_σ`-membership: both in
`A₁(S) = S_σ^# = S_F^#` is the (8.6.a) kernel TI-property; both outside is BG Theorem B(5)
(`A(S) − S_σ ⊆ ASet S U − S_σ`, a TI-subset); and the mixed cases are impossible because
`S_σ`-membership inside `S` depends only on the element's order. -/
theorem typeII_centralizerSupport_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    OddOrder.GroupTheory.IsTISubset
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
  classical
  obtain ⟨iiData⟩ := id hSII
  obtain ⟨-, -, hTI⟩ := iiData.common
  -- `S_F = S_σ` (type II) and `S_F ≠ ⊥`.
  have hMσF : maxNilpotentNormalHall S = Msigma S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hSmax
      (Or.inr hSII)
  have hFne : maxNilpotentNormalHall S ≠ ⊥ := by
    rw [hMσF]; exact Msigma_ne_bot hG hSmax
  -- `N_G(S_F) = S`: `S` normalizes its normal Hall core, the normalizer is proper (simplicity),
  -- and `S` is a coatom.
  have hNS : Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) = S := by
    have hle : S ≤ Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) := by
      intro s hs
      rw [hMσF, Msigma]
      exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (sigma S) S hs
    by_contra hne
    have hNtop : Subgroup.normalizer ((maxNilpotentNormalHall S : Subgroup G) : Set G) = ⊤ :=
      hSmax.2 _ (lt_of_le_of_ne hle fun h => hne h.symm)
    have hHnormal : (maxNilpotentNormalHall S).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (maxNilpotentNormalHall S) hHnormal with hb | ht
    · exact hFne hb
    · exact hSmax.1
        (top_le_iff.mp (ht ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le S))
  -- `IsTypeP S` and a `(κ∪σ)'`-Hall `U` with `S' = U ⊔ S_σ` (BG Lemma 15.1(b)), plus a
  -- `κ(S)`-Hall `K` (Hall's theorem in the solvable `S`), feeding Theorem B(5).
  have hP : OddOrder.BG.Ch4.S14.IsTypeP S :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hSmax (Or.inl hSII)
  obtain ⟨U, hU, hder⟩ := OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hSmax hP
  have hUM : U ≤ S :=
    (le_sup_left.trans hder.ge).trans (Subgroup.map_subtype_le _)
  have : Group.IsSolvable ↥S := hG.isSolvable_of_mem_maximalSubgroups hSmax
  obtain ⟨K', hK'⟩ :=
    OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥S) (OddOrder.BG.Ch4.S14.kappa S)
  have hKM : K'.map S.subtype ≤ S := Subgroup.map_subtype_le K'
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S)
      ((K'.map S.subtype).subgroupOf S) := by
    have hKeq : (K'.map S.subtype).subgroupOf S = K' :=
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective K'
    rw [hKeq]; exact hK'
  have hTIB := OddOrder.BG.Ch4.S16.theoremB_A_minus_Msigma_isTISubset hG hSmax hKM hUM hK hU
  -- the conjugation `g·a·g⁻¹ ∈ A(S)` for `a ∈ A(S)`, split by `S_σ`-membership.
  rintro g ⟨a, ha, hga⟩
  obtain ⟨haM', ha1, z, hzσ, hzC⟩ := ha
  obtain ⟨hgaM', hga1, w, hwσ, hwC⟩ := hga
  have haS : a ∈ S := Subgroup.map_subtype_le _ haM'
  have hgaS : g * a * g⁻¹ ∈ S := Subgroup.map_subtype_le _ hgaM'
  by_cases haσ : a ∈ Msigma S
  · by_cases hgaσ : g * a * g⁻¹ ∈ Msigma S
    · -- both in `A₁(S) = S_F^#`: the (8.6.a) kernel TI-property.
      have hg := hTI g ⟨a,
        ⟨by rw [hMσF]; exact SetLike.mem_coe.mpr haσ, by simpa using ha1⟩,
        ⟨by rw [hMσF]; exact SetLike.mem_coe.mpr hgaσ, by simpa using hga1⟩⟩
      rwa [hNS] at hg
    · -- `a ∈ S_σ`, `g·a·g⁻¹ ∉ S_σ`: impossible, `S_σ`-membership is order-determined.
      exact absurd
        ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax hgaS).mpr
          (OddOrder.BG.Ch4.S14.isPiElement_conj g
            ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax haS).mp haσ)))
        hgaσ
  · by_cases hgaσ : g * a * g⁻¹ ∈ Msigma S
    · -- `a ∉ S_σ`, `g·a·g⁻¹ ∈ S_σ`: the same order argument along `g⁻¹`.
      refine absurd ?_ haσ
      have hπ := OddOrder.BG.Ch4.S14.isPiElement_conj g⁻¹
        ((OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax hgaS).mp hgaσ)
      rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at hπ
      exact (OddOrder.BG.Ch4.S14.mem_Msigma_iff_isPiElement_sigma hG hSmax haS).mpr hπ
    · -- both in `A(S) − S_σ ⊆ ASet S U − S_σ`: BG Theorem B(5).
      have hmem : ∀ {y : G}, y ∈ S → y ∈ derivedInG S →
          ∀ {x : G}, x ∈ sharpSubgroup (Msigma S) → y ∈ Subgroup.centralizer ({x} : Set G) →
          y ∉ Msigma S →
          y ∈ OddOrder.BG.Ch4.S16.ASet S U \ ((Msigma S : Subgroup G) : Set G) := by
        intro y hyS hyM' x hxσ hxC hyσ
        refine ⟨⟨⟨hyS, fun hbot => ?_⟩, ?_⟩, fun h => hyσ (SetLike.mem_coe.mp h)⟩
        · have hxmem : x ∈ Msigma S ⊓ Subgroup.centralizer ({y} : Set G) :=
            Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hxσ.1, by
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm⟩
          rw [hbot, Subgroup.mem_bot] at hxmem
          exact hxσ.2 (Set.mem_singleton_iff.mpr hxmem)
        · exact SetLike.mem_coe.mpr (hder ▸ hyM')
      exact hTIB g ⟨a, hmem haS haM' hzσ hzC haσ, hmem hgaS hgaM' hwσ hwC hgaσ⟩

/-- The honest type-II support `A(S)` is `S`-conjugation stable (both `S' = derivedInG S` and
`S_σ = Msigma S` are normalized by `S`); the `hL_norm` input of Hypothesis (2.2). -/
theorem centralizerSupport_sharpMsigma_conj_mem [Finite G] {S : Subgroup G} {m : G}
    (hm : m ∈ S) {y : G}
    (hy : y ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) :
    m * y * m⁻¹ ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := by
  obtain ⟨hyM', hy1, x, hxσ, hyC⟩ := hy
  have hmM' : m ∈ Subgroup.normalizer ((derivedInG S : Subgroup G) : Set G) :=
    OddOrder.BG.Ch3.S10.le_normalizer_derivedInG S hm
  have hmMσ : m ∈ Subgroup.normalizer ((Msigma S : Subgroup G) : Set G) := by
    rw [Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (sigma S) S hm
  refine ⟨(Subgroup.mem_normalizer_iff.mp hmM' y).mp hyM',
    fun h => hy1 (by
      have hyeq : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hyeq, h]; group),
    m * x * m⁻¹, OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem hmMσ hxσ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
  calc m * y * m⁻¹ * (m * x * m⁻¹) = m * (y * x) * m⁻¹ := by group
    _ = m * (x * y) * m⁻¹ := by rw [hyC]
    _ = m * x * m⁻¹ * (m * y * m⁻¹) := by group

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.16) ⇒ Hypothesis (2.2) for `(A(S), S)`, Type II**: the honest type-II Dade
base.  All (8.14) signalizers are trivial — `A(S)` is a TI-subset
(`typeII_centralizerSupport_isTISubset`) — so Hypothesis (2.2) is `of_isTISubset` with
`H(a) = ⊥`.  This is the `τ_S` foundation of the (10.7) left branch: the coherence engine
(5.7) runs over the Dade isometry of this hypothesis. -/
noncomputable def typeIIDadeHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) :
    OddOrder.Peterfalvi.S04.Hypothesis G
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    (fun _y hy => OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ _, hy.2.1⟩)
    (fun _y hy => Subgroup.map_subtype_le _ hy.1)
    (fun l _a ha => centralizerSupport_sharpMsigma_conj_mem l.2 ha)
    (typeII_centralizerSupport_isTISubset hG hSmax hSII)

open OddOrder.Peterfalvi.S11 in
open scoped Classical FiniteInduce in
/-- **Peterfalvi (4.7)/(8.15), §9-family induced support, type-II instance**:
`Supp (Ind_{HU}^S ξ) ⊆ A(S) ∪ {1}` for every `ξ ∈ 𝒳` (the (9.5) family, `H ⊄ Ker ξ`), with
`A(S) = ⋃_{x∈S_σ^#} C_{S'}(x)^#` the honest (8.10) type-II support.

Generic (`TypesIIIIIIVSetup`-level) mirror of the `S15.Hypothesis`-locked
`sSet_member_support_subset_A` (whose proof this replays; the S15 instance is downstream of
this file):

* `support_induce_subset_conjugatesIntoSet`: a nonvanishing point of `Ind_{HU}^S ξ` is
  `S`-conjugate to a nonvanishing point `w ∈ HU` of `ξ`;
* the (1.2) core (`irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`,
  contrapositive) forces a nontrivial `d ∈ H` centralizing `w`; the chain
  `H = S_F = S_σ` (`TypePData.H_eq` + `maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II`)
  makes `d` an `S_σ^#`-witness, so `w ∈ A(S)` (`w ∈ HU = S'` by
  `huSub_eq_derivedInG_subgroupOf`);
* `A(S)` is `S`-conjugation invariant (`centralizerSupport_sharpMsigma_conj_mem`), so the
  original point lies in `A(S) ∪ {1}` too. -/
theorem typeII_sSet_member_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : TypesIIIIIIVSetup S)
    {ξ : IrreducibleCharacter ↥(huSub data)} (hξ : ξ ∈ xiSet data) :
    (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S ∪ {1} := by
  classical
  -- `H = S_F = S_σ` (type II).
  have hHσ : data.H = Msigma S := by
    change data.typeP.H = Msigma S
    rw [data.typeP.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG
      hSmax (Or.inr hSII)
  -- the (1.2) core: a nonvanishing `w ∈ HU` with `(w:S:G) ≠ 1` lies in `A(S)`.
  have hcore : ∀ w : ↥(huSub data),
      (ξ : ClassFunction ↥(huSub data) ℂ) w ≠ 0 → ((w : ↥S) : G) ≠ 1 →
      ((w : ↥S) : G) ∈ centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := by
    intro w hwval hwne
    have := hInHu_normal data
    have hCne : OddOrder.Peterfalvi.S03.centralizerInSubgroup (hInHu data) w ≠ ⊥ := fun hbot =>
      hwval
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
          ξ hξ hbot)
    obtain ⟨d, hd_mem, hd_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
    rw [OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup] at hd_mem
    obtain ⟨hd_H, hd_comm⟩ := hd_mem
    -- `d`'s ambient image lies in `H = S_σ`, is nontrivial, and commutes with `w`.
    have hdS_H : (d : ↥S) ∈ data.H.subgroupOf S := (Subgroup.mem_subgroupOf).mp hd_H
    have hdH_G : ((d : ↥S) : G) ∈ data.H := (Subgroup.mem_subgroupOf).mp hdS_H
    have hdG_ne : ((d : ↥S) : G) ≠ 1 := fun he => hd_ne (by
      apply Subtype.ext; apply Subtype.ext; exact he)
    have hcommG : ((d : ↥S) : G) * ((w : ↥S) : G) = ((w : ↥S) : G) * ((d : ↥S) : G) := by
      have := congrArg (fun t : ↥S => (t : G)) (Subtype.ext_iff.mp hd_comm)
      simpa using this
    -- assemble the `A(S)`-membership with witness `d ∈ S_σ^#`.
    refine ⟨?_, hwne, ((d : ↥S) : G), ?_, ?_⟩
    · have hwHU : (w : ↥S) ∈ (derivedInG S).subgroupOf S := by
        rw [← huSub_eq_derivedInG_subgroupOf]; exact w.2
      exact (Subgroup.mem_subgroupOf).mp hwHU
    · refine (Set.mem_sdiff _).mpr ⟨?_, fun he => hdG_ne (Set.mem_singleton_iff.mp he)⟩
      exact SetLike.mem_coe.mpr (hHσ ▸ hdH_G)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommG.symm
  -- assemble via `support_induce_subset_conjugatesIntoSet` + conjugation invariance.
  intro x hx
  rw [Set.mem_union, Set.mem_singleton_iff]
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  have hxsupp : (induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx_conj : x ∈ ClassFunction.conjugatesIntoSet (huSub data)
      ((ξ : ClassFunction ↥(huSub data) ℂ)).support := by
    have hind : induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ξ : ClassFunction ↥(huSub data) ℂ) := rfl
    refine ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) ?_
    rw [← hind]; exact hxsupp
  rw [ClassFunction.mem_conjugatesIntoSet] at hx_conj
  obtain ⟨c, hc, hcsupp⟩ := hx_conj
  set w : ↥(huSub data) := ⟨c⁻¹ * x * c, hc⟩ with hw_def
  have hw_val : (ξ : ClassFunction ↥(huSub data) ℂ) w ≠ 0 := ClassFunction.mem_support.mp hcsupp
  have hxeq : (x : G) = (c : G) * ((w : ↥S) : G) * (c : G)⁻¹ := by
    change (x : G) = (c : G) * ((c : G)⁻¹ * (x : G) * (c : G)) * (c : G)⁻¹
    group
  have hwne : ((w : ↥S) : G) ≠ 1 := by
    intro he
    apply hx1
    have hxG : (x : G) = 1 := by rw [hxeq, he]; group
    exact Subtype.ext hxG
  have hwA : ((w : ↥S) : G) ∈
      centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S) := hcore w hw_val hwne
  refine Or.inl ?_
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hxeq]
  exact centralizerSupport_sharpMsigma_conj_mem c.2 hwA

end DadeBase

end OddOrder.Peterfalvi.S12


