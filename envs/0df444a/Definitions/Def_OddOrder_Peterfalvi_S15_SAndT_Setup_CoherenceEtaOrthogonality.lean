-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CoherenceEtaOrthogonality
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_CoherenceEtaOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:01:56.46723+00:00
-- url     : https://prove2.me/theorems/a1f26d11-fa94-4383-b05f-6a49d5b7d98c
-- title:
--   Peterfalvi (5.3.b)/(14.9): coherent images orthogonal to the shared $\eta$-grid
-- statement:
--   Formalizes the $S$-side statement that coherent images are orthogonal to the shared $\eta$-grid (Peterfalvi (5.3.b)/(14.9)), mirroring the proven $T$-side result.
--
--   Main declarations: `coherentIndS_image_inner_eta_eq_zero` (Peterfalvi (5.3.b) / (14.9), `S`-side coherent images are orthogonal to the shared `η`-grid).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CoherenceEtaOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CoherenceEtaOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.3.b) / (14.9), `S`-side coherent images are orthogonal to the shared `η`-grid**
(the `S`-side mirror of `S16.T_typeIII_coherent_image_inner_eta_eq_zero`).

For a conjugate-closed no-real family `𝒮` of irreducible characters of the type-`P₂` maximal
`S` whose differences are `A(S) = S10.typePACore S`-supported, and a coherence
`coh : IsCoherent (Ind_S^G) 𝒮 A(S)` of the (13.2.e) induction map `τ = Ind_S^G` (`hyp.indS`),
every coherent image `coh.extension ζ` (`ζ ∈ 𝒮` irreducible) is orthogonal to the entire
`η`-grid. -/
theorem coherentIndS_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)]
    {S : Set (ClassFunction ↥hyp.S ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ζ : ClassFunction ↥hyp.S ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (coh.extension ζ) (hyp.eta i j) = 0 := by
  -- align the ambient `Fintype G`/`Invertible` with the canonical `FiniteInduce` instances that
  -- `hyp.eta` and the (3.8) engine `eta_orthogonal_of_norm_one_pair_vanish` are stated with.
  have hfintype : fintypeG = OddOrder.Peterfalvi.S12.FiniteInduce.finiteGFintype :=
    Subsingleton.elim _ _
  subst fintypeG
  have hinvertible : invertibleG = OddOrder.Peterfalvi.S12.FiniteInduce.natCardInvCG :=
    Subsingleton.elim _ _
  subst invertibleG
  classical
  have hζc : ζ.conj ∈ S := hconj hζ
  -- `ζ − ζ̄` lies in the `A(S)`-supported span of `𝒮`.
  have hdiffSpan : ζ - ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.S) S :=
    Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hdiffSupp := hsupp ζ hζ
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) :=
    ⟨hdiffSpan, hdiffSupp⟩
  -- `A(S) ⊆ A₀(S)`, so the difference is also `A₀(S)`-supported (the `dadeHypS0` support).
  have hA0Supp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
    hdiffSupp.trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono (S10.typePACore_subset_A0Set hyp.Sdata))
  -- (13.2.e) `τ = Ind_S^G` equals the `A₀(S)`-Dade image on the `A₀(S)`-supported difference.
  have hmaps : hyp.indS (ζ - ζ.conj) =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (ζ - ζ.conj) := by
    rw [hyp.indS_apply]
    exact (hyp.sInstance_dade0_eq_induce hG hnoV hA0Supp).symm
  -- the coherent conjugate difference agrees with that Dade image.
  have hextDiff : coh.extension ζ - coh.extension ζ.conj =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) (ζ - ζ.conj) := by
    rw [← hmaps, ← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  -- the crux: the difference vanishes on the saturated regular set.
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (coh.extension ζ - coh.extension ζ.conj) x = 0 := by
    intro x hx
    obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
    rw [hextDiff]
    rw [← (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) (ζ - ζ.conj)).of_isConj
        (isConj_iff.mpr ⟨g, hg⟩)]
    -- `w` is a regular `W`-element, hence a `typePV`-point of the `S`-data.
    have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
      refine ⟨?_, ?_⟩
      · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
          rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
        rw [hWeq]; exact hw.1
      · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw.2
    have hwA0 : w ∈ S10.typePACore0 hyp.S hyp.Sdata :=
      Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) hA0Supp]
    let a : {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata} := ⟨w, hwA0⟩
    have hwh : w ∈ (hyp.dadeHypS0 hG).hCoset a :=
      ⟨1, (hyp.dadeHypS0 hG).H a |>.one_mem, by simp [a]⟩
    rw [(hyp.dadeHypS0 hG).isDadeMap_dadeMap.map_eq_of_mem_hCoset _ a hwh]
    by_contra hne
    have hwSupp : (⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩ : ↥hyp.S) ∈ (ζ - ζ.conj).support :=
      ClassFunction.mem_support.mpr hne
    -- the source is `A(S)`-supported, so `w ∈ A(S) ⊆ S' = derivedInG S`.
    have hwA : w ∈ S10.typePACore hyp.S := hdiffSupp hwSupp
    have hwDeriv : w ∈ derivedInG hyp.S := S10.typePACore_subset_derived hwA
    -- but a regular `W`-element lies outside the derived subgroup.
    exact (OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.Sdata hwV) hwDeriv
  -- the straightforward `dirr`-input norms.
  have hpsiZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span hζ)
  have hconjZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζc)
  have hpsi1 : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
    rw [coh.extension_inner_eq ζ ζ (Submodule.subset_span hζ) (Submodule.subset_span hζ)]
    exact hζirr.inner_self_eq_one
  have hconj1 : ClassFunction.inner (coh.extension ζ.conj) (coh.extension ζ.conj) = 1 := by
    rw [coh.extension_inner_eq ζ.conj ζ.conj (Submodule.subset_span hζc)
      (Submodule.subset_span hζc)]
    exact hζirr.conj.inner_self_eq_one
  have hcross : ClassFunction.inner (coh.extension ζ) (coh.extension ζ.conj) = 0 := by
    rw [coh.extension_inner_eq ζ ζ.conj (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hnoReal hζ h.symm)]
  intro i j
  have h := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, star_eq_zero]
  exact h

end OddOrder.Peterfalvi.S15


