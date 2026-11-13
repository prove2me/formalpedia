-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenAlphaBound
-- name    : OddOrder_Peterfalvi_S11_NineElevenAlphaBound
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:00:36.8106+00:00
-- url     : https://prove2.me/theorems/2c9ad9e8-b7cd-4bc4-ac25-1c9e4848a143
-- title:
--   Peterfalvi (9.11.5)–(9.11.6): the $\alpha$-bound layer of the (9.11) endgame
-- statement:
--   Formalizes the $\alpha$-bound layer of the (9.11) endgame (Peterfalvi, *Character Theory for the Odd Order Theorem*, §9, pp. 56-57, (9.11.5)–(9.11.8)).
--
--   Main declarations: `sOf_H0Cprime_memberRFamily` (Per-member orthonormal `R`-family over `𝒮(H₀C′)`, `hunif`-free); `sOf_H0Cprime_memberRFamily_imageSet_of_col` (`sOf_H0Cprime_memberRFamily` reduction, column case); `SOf_memberRFamily` (Per-member orthonormal `R`-family over `S(N)`); `SOf_memberRFamily_imageSet_of_irr` (`SOf_memberRFamily` reduction, irreducible case).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenAlphaBound.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenAlphaBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSubcoherent
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IV
import Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenMackeyNorm
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTIWitness
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoBridge

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S11

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

section MemberRFamily

variable [Finite G]

/-- **Reducible `𝒮(H₀C′)`-members are certain-type column sums** (the `hunif`-free member
dichotomy, reducible half): a reducible member equals `μ_k = columnSum (muColumnChar k)`
for some `k ≠ 0` (`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` + the world-join
`muGrid_columnSum_eq_columnSum`). -/
theorem sOf_H0Cprime_reducible_eq_columnSum
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hirr : ¬ IsIrreducibleCharacter η) :
    ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := by
  have := hyp.base.finiteG
  classical
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hη
    rwa [hyp.SOf_eq] at h
  obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
    hηIKF hirr
  exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

/-- **Per-member orthonormal `R`-family over `𝒮(H₀C′)`, `hunif`-free** (mirror of
`caseB_sOf_memberRFamily` without the whole-family degree hypothesis): irreducible member →
2-element signed Dade family; reducible member → `2q`-element certain-type family
`certainTypeR` at the column of `sOf_H0Cprime_reducible_eq_columnSum`. -/
noncomputable def sOf_H0Cprime_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hη
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible: the signed Dade family
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0
    exact OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      hyp.base.dadeData.dade ⟨η, hirr⟩ hreal hdiffsupp
  · -- column: rebuild `certainTypeR` at the abstract member `η`
    have hex := sOf_H0Cprime_reducible_eq_columnSum hG hyp hη hirr
    let k := hex.choose
    have hk0 : k ≠ 0 := hex.choose_spec.1
    have hkeq : η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := hex.choose_spec.2
    exact OddOrder.Peterfalvi.S06.columnR (hyp.base.toHypothesis46 hG hG.odd)
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0) hkeq

set_option backward.isDefEq.respectTransparency false in
/-- **`sOf_H0Cprime_memberRFamily` reduction, column case** (mirror of
`caseB_sOf_memberRFamily_imageSet_of_col`). -/
theorem sOf_H0Cprime_memberRFamily_imageSet_of_col
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (sOf_H0Cprime_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  have := hyp.base.finiteG
  have hex := sOf_H0Cprime_reducible_eq_columnSum hG hyp hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold sOf_H0Cprime_memberRFamily
  rw [dif_neg hcol]
  rfl

end MemberRFamily

section SOfMemberRFamily

variable [Finite G]

/-- **Reducible `S(N)`-members are certain-type column sums** (stratum-generic
`sOf_H0Cprime_reducible_eq_columnSum`): a reducible member of any kernel-filter family
`S(N)` equals `μ_k = columnSum (muColumnChar k)` for some `k ≠ 0`
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` is already stratum-generic). -/
theorem SOf_reducible_eq_columnSum
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hirr : ¬ IsIrreducibleCharacter η) :
    ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := by
  have := hyp.base.finiteG
  classical
  have hηIKF : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (N.subgroupOf M) := by
    rwa [hyp.SOf_eq] at hη
  obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
    hηIKF hirr
  exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

/-- **Per-member orthonormal `R`-family over `S(N)`** (stratum-generic
`sOf_H0Cprime_memberRFamily`): irreducible member → 2-element signed Dade family; reducible
member → `2q`-element certain-type family `certainTypeR` at the column of
`SOf_reducible_eq_columnSum`. -/
noncomputable def SOf_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hη
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible: the signed Dade family
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0
    exact OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      hyp.base.dadeData.dade ⟨η, hirr⟩ hreal hdiffsupp
  · -- column: rebuild `certainTypeR` at the abstract member `η`
    have hex := SOf_reducible_eq_columnSum hG hyp hη hirr
    let k := hex.choose
    have hk0 : k ≠ 0 := hex.choose_spec.1
    have hkeq : η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := hex.choose_spec.2
    exact OddOrder.Peterfalvi.S06.columnR (hyp.base.toHypothesis46 hG hG.odd)
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0) hkeq

set_option backward.isDefEq.respectTransparency false in
/-- **`SOf_memberRFamily` reduction, irreducible case**. -/
theorem SOf_memberRFamily_imageSet_of_irr
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA0 M hyp.base.typeP) M),
      (SOf_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.base.dadeData.dade ⟨η, hirr⟩ hr hs).imageSet := by
  have := hyp.base.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hη)
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0, ?_⟩
  unfold SOf_memberRFamily
  rw [dif_pos hirr]

set_option backward.isDefEq.respectTransparency false in
/-- **`SOf_memberRFamily` reduction, column case**. -/
theorem SOf_memberRFamily_imageSet_of_col
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {η : ClassFunction ↥M ℂ} (hη : η ∈ hyp.SOf N)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (SOf_memberRFamily hG hyp hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  have := hyp.base.finiteG
  have hex := SOf_reducible_eq_columnSum hG hyp hη hcol
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold SOf_memberRFamily
  rw [dif_neg hcol]
  rfl

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against the
-- (5.2.e) lemmas through the `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in the
-- `H₀C′` original `sOf_H0Cprime_memberRFamily_orthogonal`)
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families, two strata** (stratum-generic
`sOf_H0Cprime_memberRFamily_orthogonal`): for members `φ ∈ S(N₁)`, `ξ ∈ S(N₂)` with
`⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the dispatched families are orthogonal — the same `2×2` case split
(irr/column).  This is the `R`-family half of the Coq `coherent_ortho` (issue 1023). -/
theorem SOf_memberRFamily_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N₁ N₂ : Subgroup G} {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ hyp.SOf N₁) (hξ : ξ ∈ hyp.SOf N₂)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (SOf_memberRFamily hG hyp hφ).Orthogonal
      (SOf_memberRFamily hG hyp hξ) := by
  have := hyp.base.finiteG
  classical
  -- typePA support for an irreducible member (needed by the μ×irr cross-orthogonality)
  have hIrrPA : ∀ {ζ : ClassFunction ↥M ℂ} {Nz : Subgroup G},
      ζ ∈ hyp.SOf Nz →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.base.typeP) M) := by
    intro ζ Nz hζ
    have hζIKF0 : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hζ)
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support ?_ hζIKF0
    intro y hyK hy1
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
    exact ⟨Subgroup.mem_subgroupOf.mp hyK,
      fun h => hy1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h))⟩
  -- self-norm `w₁ ≠ 0` of a column sum (for the μ×μ `≠`-conditions)
  have hw1ne : (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact dadeOfDiff_orthogonal_dadeOfDiff_typeP hG hyp.base ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨φ, hφirr⟩ hrφ (hIrrPA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrPA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ := SOf_memberRFamily_imageSet_of_col hG hyp hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46
    have hne1 : hyp.base.muColumnChar hG hG.odd kφ ≠ hyp.base.muColumnChar hG hG.odd kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    have hne2 : hyp.base.muColumnChar hG hG.odd kφ
        ≠ (hyp.base.muColumnChar hG hG.odd kξ)⁻¹ := by
      intro heq
      have hφξc : φ = ξ.conj := by
        rw [hkφeq, heq, ← OddOrder.Peterfalvi.S06.columnSum_conj_eq, hkξeq]
      rw [hφξc, hkξeq, OddOrder.Peterfalvi.S06.columnSum_conj_eq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46
      (hyp.base.muColumnChar_ne_one hG hG.odd hkφ0) (hyp.base.muColumnChar_ne_one hG hG.odd hkξ0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kφ)).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kξ)).symm
      hne1 hne2 α hα β hβ

end SOfMemberRFamily

end OddOrder.Peterfalvi.S13


