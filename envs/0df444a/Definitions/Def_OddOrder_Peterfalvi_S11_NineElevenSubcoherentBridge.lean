-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenSubcoherentBridge
-- name    : OddOrder_Peterfalvi_S11_NineElevenSubcoherentBridge
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:42:10.363228+00:00
-- url     : https://prove2.me/theorems/e8b03c86-73a6-4ba4-8dc4-9e26d9ff051e
-- title:
--   Peterfalvi (8.15.3)/(9.5): the subcoherence bridge from the §9 family
-- statement:
--   Formalizes the subcoherence bridge showing that the §9 family sits inside the (8.15.3) family (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8 (8.15.3), §9 (9.5), pp. 47-51), at the §9 level.
--
--   Main declarations: `sOf_degreeSubfamily_coherent_restrict` (The (8.15.3) base coherence, retargeted to the (9.5) isometry); `sOf_memberPsiDecomposition` (The per-member `ψ = 0` decomposition datum, at §9 level); `sOf_breakPsiDecomposition` (The break-member decomposition datum, at §9 level); `sOf_sixTwoDecompositionData` (The (5.2.d)/(5.2.e) decomposition supply of the (5.6) engine, at §9 level).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenSubcoherentBridge.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenSubcoherentBridge.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenBridgeBase
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenRFamily
import Definitions.Def_OddOrder_Peterfalvi_S10_SubcoherentTypeP
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTIWitness
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (8.15.3) base coherence, retargeted to the (9.5) isometry** — the `hAbase` supplier of
`sOf_nineEleven_coherent`.

`sOf_degreeSubfamily_coherent` already lands on the right *support* `A(M)`; what differs is the
map.  It carries the isometry of the `(8.15)` Dade datum `dd`, while (9.5) names the restriction of
the `(4.6.e)` datum.  Given the pin `hdd` — that `dd`'s Dade hypothesis **is** that restriction, as
it is for the intended producer — the two maps agree wherever it matters, because
`dadeIntegralCharacterMap_apply_of_support` collapses *any* `dadeIntegralCharacterMap` over a fixed
`S04.Hypothesis` to that hypothesis's own `dadeMap` on supported arguments.  The isometry data play
no role there, so no agreement between `dd.dade.fullDadeIsometryData` and
`h46.tau.restrict …` is needed — only between the underlying hypotheses. -/
theorem sOf_degreeSubfamily_coherent_restrict [Finite G] {M : Subgroup G} {A : Set G}
    (hodd : Odd (Nat.card ↥M)) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hdd : dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) (d : ℕ)
    (hKeq : h46.toCore.K = (derivedInG M).subgroupOf M)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46.toCore.subH)
    (hd0 : ((d : ℂ)) ≠ 0)
    (h2 : 2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.ncard)
    (h1A : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (h46.dade0.restrict Set.subset_union_left hAnorm)
        (h46.tau.restrict Set.subset_union_left hAnorm))
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M)) :=
  (sOf_degreeSubfamily_coherent hodd h46.toCore dd hG hM data Y d hKeq hHle hd0 h2 h1A).map
    fun c => c.congrMap fun φ hφ => by
      rw [show (OddOrder.Peterfalvi.S10.inducedNonKernelFamily_subcoherent hodd h46.toCore dd
            (fun _ hx => OddOrder.Peterfalvi.S10.inducedNonKernelFamily_mono hHle
              (hKeq ▸ sOf_subset_inducedNonKernelFamily hG hM data Y hx.1))
            (fun _ hx => hx.2.1) (fun _ hx => irrCut_conjClosed data Y d hx)).tau
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap dd.dade
            (dd.dade.fullDadeIsometryData) from rfl,
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support dd.dade _ hφ.2,
        OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
          (h46.dade0.restrict Set.subset_union_left hAnorm) _ hφ.2, hdd]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The per-member `ψ = 0` decomposition datum, at §9 level** — the `Dmem` input of the
norm-weighted (5.6) engine `S08.coherentDegreeSqNormBound_of_not_coherentW_k`.

For a member `χ` of a coherent conjugation-closed `S₁ ⊆ 𝒮(Y)`,
`CharacterPsiDecomposition.ofProjection` turns the §9 `R`-family `sOf_memberRFamily` into the
decomposition datum at `ψ = 0`.  The map is the
**coherent extension**, not `τ`: at `ψ = 0` the `ofProjection` obligation `tau1 (χ − ψ) ∈ ℤ[Irr G]`
reads `tau1 χ ∈ ℤ[Irr G]`, which is false for `τ` (the Dade map is an isometry only on the
*supported* lattice) but is exactly `IsCoherent.extension_mem_ZIrr`.

This is what lets the (5.6) engine be fed **without** `S13.sixTwoDecompositionData`, whose μ-grid
`params` exist only to manufacture these data from the §10 packaging (issue 1045). -/
noncomputable def sOf_memberPsiDecomposition [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {S₁ : Set (ClassFunction ↥M ℂ)} {A0 : Set ↥M}
    (hS₁sub : S₁ ⊆ sOf data Y)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) S₁ A0)
    {χ : ClassFunction ↥M ℂ} (hχS₁ : χ ∈ S₁)
    (hsuppχ : ((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj).support ⊆ A0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData)) χ 0 := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hχ : χ ∈ sOf data Y := hS₁sub hχS₁
  have hχc : (χ : ClassFunction ↥M ℂ).conj ∈ S₁ := hS₁conj hχS₁
  -- the two generators of the relevant lattice lie in `ℤ[S₁]`
  have hspan : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      {(χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj, (χ : ClassFunction ↥M ℂ) - 0},
      φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ := by
    intro φ hφ
    refine Submodule.span_le.mpr ?_ hφ
    rintro s (rfl | rfl)
    · exact Submodule.sub_mem _ (Submodule.subset_span hχS₁) (Submodule.subset_span hχc)
    · rw [sub_zero]; exact Submodule.subset_span hχS₁
  refine OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    ((sOf_memberRFamily hG hM data h46 hKeq htau hKsupp hχ).congrTau (by rw [htau]))
    hS₁coh.extension
    (fun φ ζ hφ hζ => hS₁coh.extension_inner_eq φ ζ (hspan φ hφ) (hspan ζ hζ))
    ((hS₁coh.extends_on_supported _ ⟨?_, hsuppχ⟩).trans (by rw [htau])) ?_ (by simp) (by simp) ?_
  · exact Submodule.sub_mem _ (Submodule.subset_span hχS₁) (Submodule.subset_span hχc)
  · rw [sub_zero]
    exact hS₁coh.extension_mem_ZIrr _ (Submodule.subset_span hχS₁)
  · -- `⟨χ, χ̄⟩ = 0`: distinct members of the `⊥`-kernel family are orthogonal, and `χ ≠ χ̄`
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hχ)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y (hS₁sub hχc)) ?_
    exact fun h => OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hχ) h.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The break-member decomposition datum, at §9 level** — the `Da` input of the norm-weighted
(5.6) engine `S08.coherentDegreeSqNormBound_of_not_coherentW_k`.

The counterpart of `sOf_memberPsiDecomposition` at the *break* member `ψ ∈ 𝒮(Y) ∖ S₁`, decomposed
against the scaled anchor `a • χ₁`.  Here `tau1` **is** `τ`: unlike the `ψ = 0` case, the
`ofProjection` obligation is `τ (ψ − a·χ₁) ∈ ℤ[Irr G]`, and the degree match makes that difference
`A₀`-supported, so `dadeIntegralCharacterMap_mem_ZIrr_of_supported` applies.  That is exactly the
asymmetry `FamilyBundleDade` records: the Dade map is a virtual-character map on the *supported*
lattice only, which covers the break datum but not the member data.

The support hypothesis `hsuppa` is the parameter carrying the degree relation `ψ(1) = a·χ₁(1)`
(via `S08.inducedKernelFamily_scaledDiff_support`); the orthogonalities come from the `⊥`-kernel
family being pairwise orthogonal, with `ψ ≠ χ₁`, `ψ̄ ≠ χ₁` supplied by the caller (`ψ ∉ S₁`,
`ψ̄ ∉ S₁`) and `ψ ≠ ψ̄` from odd order. -/
noncomputable def sOf_breakPsiDecomposition [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    {Y : Subgroup G} {ψ χ₁ : ClassFunction ↥M ℂ} (a : ℕ)
    (hψ : ψ ∈ sOf data Y) (hχ₁ : χ₁ ∈ sOf data Y)
    (hψχ₁ne : ψ ≠ χ₁) (hψcχ₁ne : (ψ : ClassFunction ↥M ℂ).conj ≠ χ₁)
    (hsuppa : ((ψ : ClassFunction ↥M ℂ) - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData)) ψ (a • χ₁) := by
  classical
  haveI := derivedInG_subgroupOf_normal M
  have hψbot := sOf_subset_inducedKernelFamily_bot hG hM data Y hψ
  have hχ₁bot := sOf_subset_inducedKernelFamily_bot hG hM data Y hχ₁
  have hψcbot := sOf_subset_inducedKernelFamily_bot hG hM data Y
    (sOf_closedUnderConjugate data Y hψ)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- the conjugate difference of `ψ` is `A₀`-supported
  have hsuppc : ((ψ : ClassFunction ↥M ℂ).conj - ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hψbot
  have hsuppc' : ((ψ : ClassFunction ↥M ℂ) - (ψ : ClassFunction ↥M ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    rw [show (ψ : ClassFunction ↥M ℂ) - (ψ : ClassFunction ↥M ℂ).conj
        = -((ψ : ClassFunction ↥M ℂ).conj - ψ) by abel, ClassFunction.support_neg]
    exact hsuppc
  -- every element of the relevant lattice is `A₀`-supported
  have hspan : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      {(ψ : ClassFunction ↥M ℂ) - (ψ : ClassFunction ↥M ℂ).conj,
        (ψ : ClassFunction ↥M ℂ) - a • χ₁},
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    intro φ hφ
    refine OddOrder.Peterfalvi.S07.support_subset_of_mem_zSpan_of_supported ?_ hφ
    rintro s (rfl | rfl)
    · exact hsuppc'
    · exact hsuppa
  have hsmulcast : (a • χ₁ : ClassFunction ↥M ℂ) = (a : ℂ) • χ₁ :=
    (Nat.cast_smul_eq_nsmul ℂ a χ₁).symm
  refine OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    ((sOf_memberRFamily hG hM data h46 hKeq htau hKsupp hψ).congrTau (by rw [htau])) _
    (fun φ ζ hφ hζ => ?_) rfl ?_ ?_ ?_ ?_
  · exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
      (hspan φ hφ) (hspan ζ hζ)
  · -- `τ (ψ − a·χ₁) ∈ ℤ[Irr G]`
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported h46.dade0
      hsuppa (Submodule.sub_mem _
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hψbot)
        (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hχ₁bot) a))
  · rw [hsmulcast, ClassFunction.inner_smul_right,
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hψbot hχ₁bot hψχ₁ne,
      mul_zero]
  · rw [hsmulcast, ClassFunction.inner_smul_right,
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hψcbot hχ₁bot hψcχ₁ne,
      mul_zero]
  · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hψbot hψcbot
      (fun h => OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (⊥ : Subgroup ↥M) hψbot h.symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (5.2.d)/(5.2.e) decomposition supply of the (5.6) engine, at §9 level** — the §9
replacement for `S13.sixTwoDecompositionData`.

Packages `sOf_breakPsiDecomposition` (the break datum `Da`) and `sOf_memberPsiDecomposition`
(the per-member data) into exactly the shape
`S08.coherentDegreeSqNormBound_of_not_coherentW_k` consumes.  All three components are immediate:

* `Da.tau1 = τ` and `D.tau1 = extension` hold by `rfl`, since `ofProjection` stores the map it is
  given;
* `D.imageFamily.Orthogonal Da.imageFamily` is `sOf_memberRFamily_orthogonal` — again by `rfl` on
  the `imageFamily` fields — with its two inner-product hypotheses supplied by pairwise
  orthogonality of the `⊥`-kernel family (`χ ≠ ψ` and `χ ≠ ψ̄` because `ψ, ψ̄ ∉ S₁ ∋ χ`).

The §13 version reaches the same data through the §10 μ-grid (`params.mu = hyp.muGrid …` and the
column machinery), which is what tied the (5.6) route to the packaging; here nothing but the §9
`R`-family dispatch is used, so **no type hypothesis appears** (issue 1045). -/
theorem sOf_sixTwoDecompositionData [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {Y : Subgroup G} {S₁ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : S₁ ⊆ sOf data Y)
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M))
    {ψ χ₁ : ClassFunction ↥M ℂ} (a : ℕ)
    (hψ : ψ ∈ sOf data Y) (hψnotS₁ : ψ ∉ S₁)
    (hψcnotS₁ : (ψ : ClassFunction ↥M ℂ).conj ∉ S₁) (hχ₁S₁ : χ₁ ∈ S₁)
    (hsuppa : ((ψ : ClassFunction ↥M ℂ) - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) :
    ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData)) ψ (a • χ₁),
      Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData) ∧
      ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData)) χ 0,
        D.imageFamily.Orthogonal Da.imageFamily ∧
        D.tau1 χ = hS₁coh.extension χ := by
  classical
  have := derivedInG_subgroupOf_normal M
  have hψbot := sOf_subset_inducedKernelFamily_bot hG hM data Y hψ
  have hψcbot := sOf_subset_inducedKernelFamily_bot hG hM data Y
    (sOf_closedUnderConjugate data Y hψ)
  refine ⟨sOf_breakPsiDecomposition hG hM data h46 hKeq htau hKsupp a hψ (hS₁sub hχ₁S₁)
    (fun h => hψnotS₁ (h ▸ hχ₁S₁)) (fun h => hψcnotS₁ (h ▸ hχ₁S₁)) hsuppa, rfl, ?_⟩
  intro χ hχS₁
  have hχ : χ ∈ sOf data Y := hS₁sub hχS₁
  have hχbot := sOf_subset_inducedKernelFamily_bot hG hM data Y hχ
  -- `χ − χ̄` is `A₀`-supported (the (6.2) conjugate-difference estimate)
  have hsuppχ : ((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    rw [show (χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj
        = -((χ : ClassFunction ↥M ℂ).conj - χ) by abel, ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp hχbot
  refine ⟨sOf_memberPsiDecomposition hG hM data h46 hKeq htau hKsupp hS₁sub hS₁conj hS₁coh
    hχS₁ hsuppχ, ?_, rfl⟩
  -- `R(χ) ⊥ R(ψ)`: the (5.2.e) cross-orthogonality at the two vanishing inner products
  exact sOf_memberRFamily_orthogonal hG hM data h46 hKeq htau hKsupp hVsub hχ hψ
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχbot hψbot
      (fun h => hψnotS₁ (h ▸ hχS₁)))
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχbot hψcbot
      (fun h => hψcnotS₁ (h ▸ hχS₁)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1) preamble, the break-member degree dictionary at §9 level**: every member
of `𝒮(H₀C′)` has degree `q·d` for a source degree `d ≤ u`.

This is the `∃ d, χ(1) = q·d ∧ d ≤ u` half of `CaseAPairBound`'s conclusion — book (9.11.1)'s
`χ(1) ≤ 2q²aχ(1) ≤ 2q²au` step reading `χ(1) = q·d` with `d = ζ(1) ≤ [HU:HC] = u` (Coq `lb01`'s
degree dictionary: `ζ|_{HC}` has a linear constituent since `(HC)′ ≤ H₀C′`).

Both ingredients are already type-free: `induceHU_apply_one_eq_q_mul` for the index factor and
`xiOf_H0Cprime_source_apply_one_le_u` for the source bound.  The §13 form
(inside `S13.nineElevenPairBound`) additionally rewrites `cprimeSub … = derivedInG hyp.C` through
`C_eq_cSub_of_noncoherent`, which is where its `hncH0C`/`htype` hypotheses enter; at §9
`chars.Cprime` *is* `cprimeSub data chief`, so that step — and with it the type hypothesis —
disappears. -/
theorem caseA_break_source_degree [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    {ψ : ClassFunction ↥M ℂ} (hψ : ψ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief)) :
    ∃ d : ℕ, ((ψ : ↥M → ℂ) 1 = ((data.q * d : ℕ) : ℂ)) ∧ d ≤ chars.u := by
  classical
  obtain ⟨ζ, hζ, rfl⟩ := hψ
  obtain ⟨d, -, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  refine ⟨d, ?_, ?_⟩
  · rw [induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  · have hduC := xiOf_H0Cprime_source_apply_one_le_u chars hζ
    rw [hdζ] at hduC
    have h := (Complex.le_def.mp hduC).1
    rw [Complex.natCast_re, Complex.natCast_re] at h
    exact_mod_cast h

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1), the (5.6) pair-bound bundle, at §9 level** — the §9 form of
`S13.NineElevenPairBound`. -/
def CaseAPairBound [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
      ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0) →
        ∃ d : ℕ, ((χ : ↥M → ℂ) 1 = ((data.q * d : ℕ) : ℂ)) ∧ d ≤ chars.u ∧
          ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
            OddOrder.Peterfalvi.S07.sumnS F
              ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.8), the equality-configuration refutation, at §9 level** — the §9
form of `S13.NineElevenEqualityRefutation`. -/
def CaseAEqualityRefutation [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) →
      2 * caseA.a = chief.p - 1 →
      chars.C = chars.Uprime →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) →
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
          χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (chief.p - 1) * ((uprimeSub data).relIndex data.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ)) →
      False

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every `𝒮(Y)`-member has positive `Snorm`**, at §9 level — the §9 form of
`S13.sOf_mem_Snorm_pos`.  The degree is `q·dζ > 0` and the squared norm is positive
(`inducedKernelFamily_inner_self_real_pos`), reached through the `⊥`-kernel world-bridge instead
of `S13.Hypothesis`. -/
theorem sOf_mem_Snorm_pos [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) {Y : Subgroup G} {χ : ClassFunction ↥M ℂ}
    (hχ : χ ∈ sOf data Y) : 0 < OddOrder.Peterfalvi.S07.Snorm χ := by
  classical
  have := derivedInG_subgroupOf_normal M
  have hpos := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hχ)
  obtain ⟨ζ, hζ, rfl⟩ := hχ
  obtain ⟨dζ, hdpos, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hdeg : (induceHU data (ζ : ClassFunction ↥(huSub data) ℂ) : ↥M → ℂ) 1
      = ((data.q * dζ : ℕ) : ℂ) := by
    rw [induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  unfold OddOrder.Peterfalvi.S07.Snorm
  apply div_pos
  · rw [hdeg, Complex.natCast_re]
    exact pow_pos (Nat.cast_pos.mpr (Nat.mul_pos hq hdpos)) 2
  · exact hpos.2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1), `𝒮₂ = 𝒮₁` — the saturated-bound subset form, at §9 level** (the §9 form
of `S13.caseA_sTwo_subset_degreeQaCut`).

At the equality configuration the maximal coherent `𝒮₂` is *contained in* the degree-`qa`
irreducible cut `𝒮₁′` of `𝒮(H₀U′)`.  The cut already sits inside `𝒮₂` (`hS₁sub` + `sOf_antitone`
along `H₀C′ ≤ H₀U′`) and **saturates** the bound `2q²au` exactly — by
`sumnS_irreducible_constant_degree` together with the (9.8.d) count equality at `C = U′` and
`2a = p−1` — so any member outside it would add its positive `Snorm` beyond `hFbound`.

No type hypothesis: §13 carries `_hG` unused and reaches finiteness through `S13.Hypothesis`;
here that is `sOf_finite` and the `⊥`-kernel bridge. -/
theorem caseA_sTwo_subset_degreeQaCut [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂)
    (hS₂sub : S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (chief.p - 1) * ((uprimeSub data).relIndex data.U))
    (hFbound : ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F
        ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ)) :
    S₂ ⊆ {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} := by
  classical
  intro χ hχS₂
  by_contra hnot
  set S1' : Set (ClassFunction ↥M ℂ) := {φ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
      IsIrreducibleCharacter φ ∧ φ 1 = ((data.q * caseA.a : ℕ) : ℂ)} with hS1'def
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  have hS1'sub : S1' ⊆ S₂ := fun φ hφ =>
    hS₁sub ⟨sOf_antitone data hle hφ.1, hφ.2.1, hφ.2.2⟩
  have hS1'fin : S1'.Finite :=
    (sOf_finite data (chief.H0 ⊔ uprimeSub data)).subset fun _ hφ => hφ.1
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ) * ((data.q * caseA.a : ℕ) : ℝ) ^ 2 :=
    sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hrelu : (uprimeSub data).relIndex data.U = chars.u := by
    have hUpC : cSub data chief = uprimeSub data := hCUprime
    rw [← hUpC]
    exact relIndex_cSub_U_eq_u _
  have hcount' : S1'.ncard * (caseA.a * caseA.a) = 2 * caseA.a * chars.u := by
    rw [hcount, hrelu, ← h2a]
  have hsatur : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    have hcast : ((S1'.ncard : ℝ)) * ((caseA.a : ℝ) * (caseA.a : ℝ))
        = 2 * (caseA.a : ℝ) * ((chars.u : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount'
    rw [hsum1', ← Set.ncard_eq_toFinset_card _ hS1'fin, Nat.cast_mul]
    linear_combination ((data.q : ℝ) ^ 2) * hcast
  have hχnot : χ ∉ hS1'fin.toFinset := fun hmem => hnot (hS1'fin.mem_toFinset.mp hmem)
  have hFsub : ↑(insert χ hS1'fin.toFinset) ⊆ S₂ := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hχS₂ (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
  have hbound := hFbound _ hFsub
  have hsplit : OddOrder.Peterfalvi.S07.sumnS (insert χ hS1'fin.toFinset)
      = OddOrder.Peterfalvi.S07.Snorm χ
        + OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset := by
    unfold OddOrder.Peterfalvi.S07.sumnS
    exact Finset.sum_insert hχnot
  rw [hsplit, hsatur] at hbound
  linarith [sOf_mem_Snorm_pos hG hM data (hS₂sub hχS₂)]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction, at §9 level** — the §9 form of
`S13.NineElevenSTwoExtraction`: at the equality configuration every `𝒮₂`-member has degree `qa`.

This is the `hS2deg` consumed by the (9.11.2) TI-witness and the (9.11.3) count. -/
def CaseASTwoExtraction [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) →
      2 * caseA.a = chief.p - 1 →
      chars.C = chars.Uprime →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) →
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
          χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (chief.p - 1) * ((uprimeSub data).relIndex data.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ)) →
      ∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `𝒮₂ = 𝒮₁` extraction, discharged at §9 level** — the degree form of
`caseA_sTwo_subset_degreeQaCut`, i.e. the §9 form of `S13.nineElevenSTwoExtraction`.

Like the §13 original this is a one-liner over the subset form; unlike it, no type hypothesis is
in play anywhere on the route. -/
theorem caseA_sTwoExtraction [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) :
    CaseASTwoExtraction caseA tau A0 := by
  intro S₂ hS₁sub hS₂sub _hS₂conj _hS₂coh _hS₃ne _hpairs h2a hCUprime _hS3deg hcount hFbound χ hχ
  exact (caseA_sTwo_subset_degreeQaCut hG hM caseA hS₁sub hS₂sub h2a hCUprime hcount
    hFbound hχ).2.2

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi's `𝒮₄`, at §9 level** — the §9 form of `S13.nineElevenSFour`: the irreducible
members of `𝒮(H₀C)` outside `𝒮₂`, whose cardinality the (9.11.5)–(9.11.8) argument bounds by
`‖α‖²`. -/
noncomputable def caseASFour [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) (S₂ : Set (ClassFunction ↥M ℂ)) :
    Set (ClassFunction ↥M ℂ) :=
  {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) | IsIrreducibleCharacter φ ∧ φ ∉ S₂}

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8), the norm bound, at §9 level** — the §9 form of
`S13.NineElevenNormBound`.

Book (9.11.4): `α = Ind_{HU₁}^M 1 − ψ₁` has `‖α‖² = a + 1 + (q−1)a²/u`, in cleared form
`N·u = (a+1)·u + (q−1)·a²`; and (9.11.5)–(9.11.8) give `|𝒮₄| ≤ ‖α‖² = N`, since distinct
`𝒮₄`-members would otherwise consume overlapping unit slices of `α^τ` and let a pair be
coherently adjoined. -/
def CaseANormBound [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) →
      2 * caseA.a = chief.p - 1 →
      chars.C = chars.Uprime →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) →
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
          χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (chief.p - 1) * ((uprimeSub data).relIndex data.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ)) →
      (∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) →
      ∃ N : ℕ,
        N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 ∧
        (caseASFour data chief S₂).ncard ≤ N

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The degree-`qa` base subfamily of `𝒮(H₀C′)` has at least two members** — the `h2` input of
`sOf_nineEleven_coherent`, discharged.

The (9.8.d) count is exact and its lower bound `(p−1)·[U:U′]` is positive (`p` prime,
`0 < u ≤ [U:U′]`), so the degree-`qa` irreducible cut of `𝒮(H₀U′)` is nonempty
(`caseA_character_count_exact`); `sOf_antitone` along `H₀C′ ≤ H₀U′` moves the witness into
`𝒮(H₀C′)`, and `irrCut_two_le_ncard` doubles it with its conjugate.

This is the same route §13 takes inside `S13.caseA_coherent_sOf_H0Cprime_of_refuter`, which is why
the §9 chain need not expose `h2` after all — every input on it is §9-level and type-free. -/
theorem caseA_irrCut_two_le_ncard [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
      IsIrreducibleCharacter φ ∧
      ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))}.ncard := by
  classical
  -- positivity of the (9.8.d) lower bound `(p−1)·[U:U′]`
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  have hrel : 0 < (uprimeSub data).relIndex data.U :=
    lt_of_lt_of_le (u_odd hG chars).pos (u_le_relIndex_uprimeSub_U chars)
  have hNpos := lt_of_lt_of_le (Nat.mul_pos hp1 hrel) (caseA_character_count_exact hG caseA)
  have hne : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`)
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  obtain ⟨φ, hφ, hφirr, hφdeg⟩ := hne
  exact irrCut_two_le_ncard hG hM data (chief.H0 ⊔ cprimeSub data chief) (data.q * caseA.a)
    ⟨φ, sOf_antitone data hle hφ, hφirr, hφdeg⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.2), the two-summand inertia inputs, at §9 level** — the §9 form of
`S13.caseA_two_summand_inertia_inputs`: at the equality configuration there are `K₁, K₂` of
relative index `a` in `U` with `C = K₁ ⊓ K₂` (whence `u ≤ a²`).

Every `𝒮(H₀C)`-member has degree `qu` or `qa`, by `sOf_antitone` along `H₀C′ ≤ H₀C` and the
`𝒮₃`/`𝒮₂` degree facts; `nineElevenTwo_two_summand_inertia` turns that dichotomy into the inertia
identity.

⚠ This is the step where §13 needs `hncH0C`/`htype`: it rewrites `C = cSub` through
`C_eq_cSub_of_noncoherent` to see `C′ ≤ C`.  At §9 `chars.C` *is* `cSub data chief`, so the
rewrite — and with it the type hypothesis — is gone. -/
theorem caseA_two_summand_inertia_inputs [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    ∃ K₁ K₂ : Subgroup G,
      K₁.relIndex data.U = caseA.a ∧ K₂.relIndex data.U = caseA.a ∧
      chars.C = K₁ ⊓ K₂ := by
  refine nineElevenTwo_two_summand_inertia caseA ?_
  intro φ hφ
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
    sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
  have hφ' : φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := sOf_antitone data hle hφ
  by_cases hφS₂ : φ ∈ S₂
  · exact Or.inr (hS2deg φ hφS₂)
  · exact Or.inl (hS3deg φ ⟨hφ', hφS₂⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.3), the count inputs, at §9 level** — the §9 form of
`S13.caseA_nineElevenThree_count_inputs`: the `𝒳(H₀C)` class equation with its degree-`u`
character count already split into `W₁`-orbits,
`u + (|𝒮₄|·q + (p−1))·u² + q(p−1)·u = p^q·u`.

Two containments feed `nineElevenThree_orbit_split`: `H₀C′ ≤ H₀U′` (from `C′ = [C,C] ≤ [U,U] = U′`)
and `H₀C′ ≤ H₀C` (from `C′ ≤ C`).  §13 needs `hncH0C`/`htype` for the second — it rewrites
`C = cSub` first — and at §9 that rewrite is definitional, so neither hypothesis appears. -/
theorem caseA_nineElevenThree_count_inputs [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₁sub : {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂)
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
      = (chief.p - 1) * ((uprimeSub data).relIndex data.U)) :
    chars.u + ((caseASFour data chief S₂).ncard * data.q + (chief.p - 1)) * chars.u ^ 2
        + data.q * (chief.p - 1) * chars.u
      = chief.p ^ data.q * chars.u := by
  classical
  have hleU' : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  have hleC : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
    sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
  have hS₁'sub : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁sub ⟨sOf_antitone data hleU' hχ.1, hχ.2.1, hχ.2.2⟩
  have hS3deg' : ∀ χ ∈ sOf data (chief.H0 ⊔ cSub data chief), χ ∉ S₂ →
      χ 1 = ((data.q * chars.u : ℕ) : ℂ) :=
    fun χ hχ hnot => hS3deg χ ⟨sOf_antitone data hleC hχ, hnot⟩
  exact nineElevenThree_orbit_split hG caseA hS₁'sub hS3deg' hS2deg hCUprime hcount

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.5): the equality refutation, at §9 level** — the §9 form of
`S13.nineElevenEqualityRefutation_of_sTwoExtraction_normBound`.

Assembles `CaseAEqualityRefutation` from the two Phase-D/E carriers: the `𝒮₂ = 𝒮₁` degree
extraction and the `|𝒮₄| ≤ ‖α‖²` norm bound.  Phases B and C are the §9 lemmas above
(`caseA_two_summand_inertia_inputs`, `caseA_nineElevenThree_count_inputs`), and the arithmetic
spine `nineElevenCaseA_equality_refutation` was already §9-level and type-free.  `hn` is
definitional here (`n = |𝒮₄|·q + (p−1)` by construction), with `3 ≤ q`, `1 ≤ u` and `p = 2a+1`
supplied on the spot.

**No `hncH0C`/`htype`**: §13 threads them only into Phases B and C, and both shed them at §9. -/
theorem caseA_equalityRefutation_of_sTwoExtraction_normBound [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M)
    (hext : CaseASTwoExtraction caseA tau A0)
    (hnb : CaseANormBound caseA tau A0) :
    CaseAEqualityRefutation caseA tau A0 := by
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound
  have hS2deg := hext S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg
    hcount hFbound
  obtain ⟨N, hnorm, hleN⟩ := hnb S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime
    hS3deg hcount hFbound hS2deg
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    caseA_two_summand_inertia_inputs caseA hS3deg hS2deg
  have hclass := caseA_nineElevenThree_count_inputs hG caseA hS₁sub hS3deg hS2deg
    hCUprime hcount
  have hqp : (data.q).Prime := data.nontrivial.2.1
  have hqodd : Odd data.q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.typeP.W1)
  have hq3 : 3 ≤ data.q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu : 1 ≤ chars.u := (u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  exact nineElevenCaseA_equality_refutation caseA hq3 hu hpeq hK₁ hK₂ hCinf hclass rfl
    hnorm hleN

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.2), the TI-witness, at §9 level** — the §9 form of
`S13.caseA_nineElevenTwo_tiWitness`: at the equality configuration there is `U₁` with
`C ≤ U₁ ≤ U`, `[U:U₁] = a`, and the TI property.

Same shape as `caseA_two_summand_inertia_inputs`: the `𝒮(H₀C)` degree dichotomy (`qu` on `𝒮₃`,
`qa` on `𝒮₂`) feeds `nineElevenTwoTIWitness_of_degree_dichotomy`, and the `H₀C′ ≤ H₀C`
containment that §13 obtains by rewriting `C = cSub` is definitional here — so `hncH0C`/`htype`
are again absent. -/
theorem caseA_nineElevenTwo_tiWitness [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ))
    (hS2deg : ∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    NineElevenTwoTIWitness caseA := by
  refine nineElevenTwoTIWitness_of_degree_dichotomy caseA ?_
  intro φ hφ
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
    sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
  have hφ' : φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := sOf_antitone data hle hφ
  by_cases hφS₂ : φ ∈ S₂
  · exact Or.inr (hS2deg φ hφS₂)
  · exact Or.inl (hS3deg φ ⟨hφ', hφS₂⟩)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.7)–(9.11.8), the coherent-pair refutation, at §9 level** — the §9 form of
`S13.NineElevenSevenEightRefutation`.

This is the residual to which §13 reduces the whole case (9.7.a) equality configuration: in the
(9.11.6) dichotomy's *zero* branch, `α^τ ⊥ 𝒮₃^{τ₃}`, and this carrier is what refutes it.

⚠ Unlike `S13.NineElevenSevenEightRefutation`, the norm value `N = ‖α‖²` of (9.11.4) is taken as a
parameter (`hnorm`).  The §13 producer rebuilds the whole `γ = Ind_{HU₁}^M 1` context a second time
just to recover it for the `𝒮₄ ≠ ∅` step; here the only consumer
(`caseA_normBound_of_sevenEightRefutation`) already has `N` and its Mackey identity in scope at the
point of use, so passing it removes the duplication.  This matches the book, where (9.11.7) is
argued inside the (9.11.4)–(9.11.6) context. -/
def CaseASevenEightRefutation [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M) : Prop :=
  ∀ S₂ : Set (ClassFunction ↥M ℂ),
    {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
      S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) →
      2 * caseA.a = chief.p - 1 →
      chars.C = chars.Uprime →
      (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
        (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) →
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
          χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
        = (chief.p - 1) * ((uprimeSub data).relIndex data.U) →
      (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ)) →
      (∀ χ ∈ S₂, (χ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) →
      ∀ N : ℕ,
        N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 →
      ∀ c₃ : OddOrder.Peterfalvi.S07.IsCoherent tau
        (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂) A0,
      ∀ γ ψ₁ : ClassFunction ↥M ℂ,
        ψ₁ ∈ S₂ →
        IsIrreducibleCharacter ψ₁ →
        ((ψ₁ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) →
        γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M →
        ((γ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) →
        (∀ φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief), ClassFunction.inner γ φ = 0) →
        ((γ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 →
        (∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
          ClassFunction.inner (tau (γ - ψ₁)) (c₃.extension lam) = 0) →
        False

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1): the case (9.7.a) maximality refuter, at §9 level** — the `hArefute`
input of `sOf_nineEleven_coherent`, reduced to the two honest (9.11) carriers.

The §9 form of `S13.caseA_refuter_of_equality_refutation`, with `tau`/`A0` as parameters and every
`S13.Hypothesis` alias replaced by its §9 original.  The argument is unchanged — the (9.11.1)
squeeze: per non-adjoinable `χ ∈ 𝒮₃`, `hbound` gives source degree `d ≤ u` and the upper bound
`sumnS 𝒮₁′ ≤ 2q²a·d` on the degree-`qa` subfamily transported from `𝒮(H₀U′)` along `H₀C′ ≤ H₀U′`;
`sumnS_irreducible_constant_degree` gives the matching lower bound; `nineElevenOne_configuration`
closes the circle, and `hrefuteEq` refutes the resulting equality configuration. -/
theorem caseA_refuter_of_equality_refutation [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M)
    (hbound : CaseAPairBound caseA tau A0)
    (hrefuteEq : CaseAEqualityRefutation caseA tau A0) :
    ∀ S₂ : Set (ClassFunction ↥M ℂ),
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
          IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
        S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
        (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
        (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
          ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) → False := by
  classical
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hu : 0 < chars.u := (u_odd hG chars).pos
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`)
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  -- the uniform degree-`qa` subfamily `𝒮₁′ ⊆ 𝒮(H₀U′)`
  have hS1'sub : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁sub ⟨sOf_antitone data hle hχ.1, hχ.2.1, hχ.2.2⟩
  have hS1'fin : ({χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}).Finite :=
    (sOf_finite data _).subset fun _ hχ => hχ.1
  -- (9.11.5) left endpoint: `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²`
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ) * ((data.q * caseA.a : ℕ) : ℝ) ^ 2 :=
    sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hs1' : (({χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard : ℝ)) * ((data.q * caseA.a : ℕ) : ℝ) ^ 2
      ≤ OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset :=
    le_of_eq (by rw [Set.ncard_eq_toFinset_card _ hS1'fin, hsum1'])
  -- per-`χ` (9.11.1) squeeze
  have hconfig : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∃ d : ℕ, ((χ : ↥M → ℂ) 1 = ((data.q * d : ℕ) : ℂ)) ∧
        (2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ d = chars.u ∧
          {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
              χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard * (caseA.a * caseA.a)
            = (chief.p - 1) * ((uprimeSub data).relIndex data.U)) ∧
        (∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
          OddOrder.Peterfalvi.S07.sumnS F
            ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)) := by
    intro χ hχ
    obtain ⟨d, hχdeg, hdu, hFbound⟩ :=
      hbound S₂ hS₁sub hS₂sub hS₂conj hS₂coh χ hχ (hpairs χ hχ)
    have hpair : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
        ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) :=
      hFbound hS1'fin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
    exact ⟨d, hχdeg, nineElevenOne_configuration hG caseA hq hu hp1 hdu hs1' hpair, hFbound⟩
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  obtain ⟨d₀, -, ⟨h2a, hCUprime, hd₀u, hcount⟩, hFbound₀⟩ := hconfig χ₀ hχ₀
  have hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨d, hχdeg, ⟨-, -, hdu, -⟩, -⟩ := hconfig χ hχ
    rwa [hdu] at hχdeg
  have hFboundU : ∀ F : Finset (ClassFunction ↥M ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F
        ≤ 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    intro F hF
    have h := hFbound₀ F hF
    rwa [hd₀u] at h
  exact hrefuteEq S₂ hS₁sub hS₂sub hS₂conj hS₂coh ⟨χ₀, hχ₀⟩ hpairs
    h2a hCUprime hS3deg hcount hFboundU

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (8.15.3) base coherence, lifted to the `A₀`-support** — the `hAbase` supplier of
`sOf_nineEleven_coherent`.

`sOf_degreeSubfamily_coherent_restrict` delivers the degree-`d` cut's coherence on `A(M)`; (9.11)
runs both Clifford branches on `A₀ = A ∪ V^M` (case (a) has no choice — see `caseA_pairBound`), so
the support has to be enlarged and the map moved to the `A₀`-datum.

Enlarging is `S07.isCoherent_of_supportedSpan_le`, whose containment
`ℤ[S, A₀] ⊆ ℤ[S, A]` holds because the cut has **uniform degree**: `1 ∉ A₀` forces an
`A₀`-supported lattice element to vanish at `1`, hence (by
`S08.mem_span_scaledDiff_of_mem_zSupportedSpan`) to be a combination of member differences, each
`A`-supported by the (4.7) estimate `S10.inducedNonKernelFamily_diff_support`.  Moving the map is
`IsCoherent.congrMap` through `S08.dadeIntegralCharacterMap_restrict_eq_of_support`, the same
restriction identity the case (b) descent uses in the opposite direction. -/
theorem sOf_degreeSubfamily_coherent_A0 [Finite G] {M : Subgroup G} {A : Set G}
    (hodd : Odd (Nat.card ↥M)) (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hdd : dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm)
    (_htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) (d : ℕ)
    (hKeq : h46.toCore.K = (derivedInG M).subgroupOf M)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46.toCore.subH)
    (hd0 : ((d : ℂ)) ≠ 0)
    (h2 : 2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.ncard)
    (h1A : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) := by
  classical
  set S : Set (ClassFunction ↥M ℂ) := {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
    IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} with hSdef
  have h1A0 : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup
      (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := fun h =>
    (OddOrder.Peterfalvi.S04.mem_sharp.mp
      (h46.dade0.subset_sharp (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h))).2 rfl
  -- an anchor in the cut (the `2 ≤ ncard` count)
  have hSne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨χ₁, hχ₁⟩ := hSne
  have hmemNK : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ S →
      x ∈ OddOrder.Peterfalvi.S10.inducedNonKernelFamily h46.toCore.K h46.toCore.subH :=
    fun {_} hx => OddOrder.Peterfalvi.S10.inducedNonKernelFamily_mono hHle
      (hKeq ▸ sOf_subset_inducedNonKernelFamily hG hM data Y hx.1)
  -- `ℤ[S, A₀] ⊆ ℤ[S, A]`: uniform degree + `1 ∉ A₀`
  have hle : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup A M) := by
    intro φ hφ
    refine ⟨hφ.1, ?_⟩
    have hspan := OddOrder.Peterfalvi.S08.mem_span_scaledDiff_of_mem_zSupportedSpan h1A0
      (χ₁ := χ₁) (by rw [hχ₁.2.2]; exact hd0)
      (fun f hf => ⟨1, by rw [hf.2.2, hχ₁.2.2]; push_cast; ring⟩) hφ
    have hsub : Submodule.span ℤ {g : ClassFunction ↥M ℂ | ∃ f ∈ S, ∃ n : ℕ,
        (f : ↥M → ℂ) 1 = (n : ℂ) * (χ₁ : ↥M → ℂ) 1 ∧ g = f - n • χ₁} ≤
        (ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
          (OddOrder.Peterfalvi.S04.supportInSubgroup A M)).restrictScalars ℤ := by
      refine Submodule.span_le.mpr ?_
      rintro g ⟨f, hf, n, hfn, rfl⟩
      have hn1 : n = 1 := by
        have h : (d : ℂ) = (n : ℂ) * (d : ℂ) := by
          conv_lhs => rw [← hf.2.2]
          rw [hfn, hχ₁.2.2]
        have h1 : (1 : ℂ) * (d : ℂ) = (n : ℂ) * (d : ℂ) := by rw [one_mul]; exact h
        exact_mod_cast (mul_right_cancel₀ hd0 h1).symm
      subst hn1
      simp only [one_smul, SetLike.mem_coe, Submodule.restrictScalars_mem,
        ClassFunction.mem_supportedSubmodule]
      exact OddOrder.Peterfalvi.S10.inducedNonKernelFamily_diff_support h46.toCore
        (hmemNK hf) (hmemNK hχ₁) (by rw [hf.2.2, hχ₁.2.2])
    exact hsub hspan
  -- witness on `A₀`: any member difference is `A`-supported, hence `A₀`-supported
  have hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) ∧ φ ≠ 0 := by
    obtain ⟨χ₂, hχ₂, hne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < S.ncard) χ₁
    refine ⟨χ₂ - χ₁, ⟨Submodule.sub_mem _ (Submodule.subset_span hχ₂)
      (Submodule.subset_span hχ₁), ?_⟩, sub_ne_zero.mpr hne⟩
    exact (OddOrder.Peterfalvi.S10.inducedNonKernelFamily_diff_support h46.toCore
      (hmemNK hχ₂) (hmemNK hχ₁) (by rw [hχ₂.2.2, hχ₁.2.2])).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  exact ((sOf_degreeSubfamily_coherent_restrict hodd h46 dd hAnorm hdd hG hM data Y d
    hKeq hHle hd0 h2 h1A).map fun c =>
      (OddOrder.Peterfalvi.S07.isCoherent_of_supportedSpan_le c hle hwit).congrMap
        (fun φ hφ =>
          OddOrder.Peterfalvi.S08.dadeIntegralCharacterMap_restrict_eq_of_support h46.dade0
            h46.tau Set.subset_union_left hAnorm (hle hφ).2))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.1), the (5.6) pair-bound bundle, discharged at §9 level** — the `hbound`
input of `sOf_nineEleven_coherent`.

The §9 form of `S13.nineElevenPairBound`, and the point at which case (9.7.a) becomes type-free:
§13 needs `hncH0C`/`htype` only to rewrite `cprimeSub … = derivedInG hyp.C`, and reaches the
(5.2.d)/(5.2.e) data through the §10 μ-grid.  Here the first is definitional and the second is
`sOf_sixTwoDecompositionData`, built from the §9 `R`-family dispatch.

The argument is book (9.11.1)'s right endpoint unchanged: the break member has degree `q·d` with
`d ≤ u` (`caseA_break_source_degree`); the anchor is a degree-`qa` irreducible of `𝒮(H₀U′)`,
which the (9.8.d) count `caseA_character_count_exact` makes nonempty, transported along
`H₀C′ ≤ H₀U′`; and the norm-weighted engine bounds `∑ deg²/‖·‖² ≤ 2e`, which rescales by the
anchor degree `(qa)²` to `sumnS F ≤ 2q²a·d`.

⚠ Two syntactically distinct forms of the same `τ` meet here: the `R`-families are produced for
`h46.tau` (`certainTypeR` fixes that), while the engine hardcodes
`h46.dade0.fullDadeIsometryData`.  The decomposition data are already transported (via
`OrthonormalCharacterImageFamily.congrTau`), and the coherence crosses by `IsCoherent.congrMap`,
which keeps `.extension` *definitionally* — that is what lets the per-member clauses
`(Dmem i).tau1 = hS₁.extension` still typecheck.  Rewriting the hypotheses instead does not work:
`rw [htau] at cohS₂` rebinds it and strands the already-derived clauses. -/
theorem caseA_pairBound [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G)) :
    CaseAPairBound caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) := by
  classical
  have := derivedInG_subgroupOf_normal M
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh ψ hψ hnc
  obtain ⟨hψS, hψnotS₂⟩ := hψ
  obtain ⟨cohS₂⟩ := hS₂coh
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  set A0 : Set ↥M := OddOrder.Peterfalvi.S04.supportInSubgroup
    (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M with hA0def
  obtain ⟨d, hψdegq, hdu⟩ := caseA_break_source_degree chars hψS
  refine ⟨d, hψdegq, hdu, ?_⟩
  obtain ⟨e, hψdegqae⟩ := OddOrder.Peterfalvi.S11.caseA_sOf_source_degree_ratio caseA hψS
  have he : d = caseA.a * e := by
    have h : ((data.q * d : ℕ) : ℂ) = ((data.q * (caseA.a * e) : ℕ) : ℂ) := by
      rw [← hψdegq, hψdegqae]; push_cast; ring
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.cast_inj.mp h)
  -- the anchor: a degree-`qa` irreducible of `𝒮(H₀U′)`, transported into `S₂`
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  have hrel : 0 < (uprimeSub data).relIndex data.U :=
    lt_of_lt_of_le (u_odd hG chars).pos (u_le_relIndex_uprimeSub_U chars)
  have hNpos := lt_of_lt_of_le (mul_pos hp1 hrel) (caseA_character_count_exact hG caseA)
  have hne : {φ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter φ ∧
      φ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  obtain ⟨χ₁, hχ₁sOfU', hχ₁irr, hχ₁deg⟩ := hne
  have hχ₁S₂ : χ₁ ∈ S₂ := hS₁sub ⟨sOf_antitone data hle hχ₁sOfU', hχ₁irr, hχ₁deg⟩
  have hSfin := sOf_finite data (chief.H0 ⊔ cprimeSub data chief)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂sub
  obtain ⟨k, χmem, hinj, hrange⟩ := OddOrder.Peterfalvi.S08.exists_finEnum_general hS₂fin
  have hmemS1set : ∀ j, χmem j ∈ S₂ := fun j => hrange ▸ Set.mem_range_self j
  obtain ⟨i₁, hi₁eq⟩ := (hrange ▸ hχ₁S₂ : χ₁ ∈ Set.range χmem)
  subst hi₁eq
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  have hS₂bot : S₂ ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun _ hx => hIKF (hS₂sub hx)
  have hmemfam : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun j => hS₂bot (hmemS1set j)
  have hψbot := hIKF hψS
  have hψcnotS₂ : (ψ : ClassFunction ↥M ℂ).conj ∉ S₂ := by
    intro hc
    exact hψnotS₂ (by simpa using hS₂conj hc)
  choose deg hdeg using fun j : Fin k =>
    OddOrder.Peterfalvi.S11.caseA_sOf_source_degree_ratio caseA (hS₂sub (hmemS1set j))
  have hdeg_anchor : ∀ j, (χmem j : ↥M → ℂ) 1 = (deg j : ℂ) * (χmem i₁ : ↥M → ℂ) 1 := by
    intro j
    rw [hdeg j, hχ₁deg]
    push_cast
    ring
  have ha1 : deg i₁ = 1 := by
    have h : data.q * caseA.a * 1 = data.q * caseA.a * deg i₁ := by
      rw [mul_one]
      exact Nat.cast_inj.mp (hχ₁deg.symm.trans (hdeg i₁))
    exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq caseA.a_pos) h).symm
  have hψdeg : (ψ : ↥M → ℂ) 1 = (e : ℂ) * (χmem i₁ : ↥M → ℂ) 1 := by
    rw [hψdegqae, hχ₁deg]
    push_cast
    ring
  have hdiffasuppψ : ((ψ : ClassFunction ↥M ℂ) - e • χmem i₁).support ⊆ A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp hψbot
      (hmemfam i₁) hψdeg
  obtain ⟨Da, hDatau1, hdatum⟩ := sOf_sixTwoDecompositionData hG hM data h46 hKeq htau
    hKsupp hVsub hS₂sub hS₂conj cohS₂ e hψS hψnotS₂ hψcnotS₂ (hmemS1set i₁) hdiffasuppψ
  choose Dfun hDorth hDtau using hdatum
  obtain ⟨-, hψψne, hψbψbne, hψbψ, hψψb, hdiffsuppψ, hψ_S1, hψbar_S1⟩ :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_breakChar_fields hModd hKsupp hS₂bot hψbot
      hψnotS₂ hψcnotS₂
  have hmemdegdiffsupp : ∀ i : Fin k, i ∈ (Finset.univ : Finset (Fin k)) →
      ((χmem i - deg i • χmem i₁).support ⊆ A0) := fun i _ =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp (hmemfam i)
      (hmemfam i₁) (hdeg_anchor i)
  have htau1ψ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0
      (h46.dade0.fullDadeIsometryData)
      ((ψ : ClassFunction ↥M ℂ) - e • χmem i₁) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      h46.dade0 hdiffasuppψ ?_
    exact Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hψbot)
      (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hmemfam i₁)) e)
  have hcover : ∀ x ∈ S₂, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
      hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : ((ψ : ClassFunction ↥M ℂ).conj : ↥M → ℂ) 1 = (ψ : ↥M → ℂ) 1 := by
    rw [ClassFunction.conj_apply, hψdegq]
    exact star_natCast _
  have hχ₁ne : (χmem i₁ : ↥M → ℂ) 1 ≠ 0 := by
    rw [hχ₁deg]
    exact Nat.cast_ne_zero.mpr (Nat.mul_pos hq caseA.a_pos).ne'
  have h1A0 : (1 : ↥M) ∉ A0 := fun h =>
    (OddOrder.Peterfalvi.S04.mem_sharp.mp
      (h46.dade0.subset_sharp (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h))).2 rfl
  have hgen :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (χ := (ψ : ClassFunction ↥M ℂ)) (chibar := (ψ : ClassFunction ↥M ℂ).conj)
      (chi1 := χmem i₁) (a := e) hSgen hψdeg hbar1 hχ₁ne h1A0
  have hmcpos : ∀ j, 0 < (ClassFunction.inner (χmem j) (χmem j)).re := fun j =>
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam j)).2
  have hmemortho : ∀ i j, ClassFunction.inner (χmem i) (χmem j)
      = @ite ℂ (i = j) (Classical.propDecidable (i = j))
          (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam i)).1
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hmemfam i) (hmemfam j) (fun h => hij (hinj h))
  -- cross the two `τ`-forms: `congrMap` keeps `.extension` definitionally.  ⚠ inline, not `have`:
  -- `IsCoherent` is data, so a `have` makes `.extension` opaque and strands the `hDtau` clauses.
  rw [htau] at hnc
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSqNormBound_of_not_coherentW_k
    h46.dade0 (cohS₂.congrMap (fun φ _ => by rw [htau])) (ψ : ClassFunction ↥M ℂ)
    hdiffsuppψ hψψne hψbψbne hψψb hψbψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    hmemdegdiffsupp (fun j _ => hmemS1set j)
    (fun j => (ClassFunction.inner (χmem j) (χmem j)).re) (fun j _ => hmcpos j)
    (fun i _ j _ => hmemortho i j)
    (fun i _ => Dfun (χmem i) (hmemS1set i)) Da hDatau1
    (fun i _ => hDorth (χmem i) (hmemS1set i))
    (fun i _ => hDtau (χmem i) (hmemS1set i))
    hdiffasuppψ htau1ψ ha1 hSgen hgen hnc
  intro F hF
  have hFsub : F ⊆ hS₂fin.toFinset := fun _ hφ => hS₂fin.mem_toFinset.mpr (hF hφ)
  have henum : OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset
      = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := by
    rw [OddOrder.Peterfalvi.S07.sumnS,
      show hS₂fin.toFinset = (Set.range χmem).toFinset by
        ext φ; rw [Set.Finite.mem_toFinset, Set.mem_toFinset, hrange],
      OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hinj]
  have hsnorm : ∀ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j)
      = ((deg j : ℝ) * ((data.q * caseA.a : ℕ) : ℝ)) ^ 2
        / (ClassFunction.inner (χmem j) (χmem j)).re := by
    intro j
    unfold OddOrder.Peterfalvi.S07.Snorm
    congr 1
    rw [hdeg j, Complex.natCast_re]
    push_cast
    ring
  calc OddOrder.Peterfalvi.S07.sumnS F
      ≤ OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset :=
        OddOrder.Peterfalvi.S07.sumnS_le_of_subset hFsub
    _ = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := henum
    _ = ∑ j : Fin k, ((deg j : ℝ) * ((data.q * caseA.a : ℕ) : ℝ)) ^ 2
          / (ClassFunction.inner (χmem j) (χmem j)).re :=
        Finset.sum_congr rfl (fun j _ => hsnorm j)
    _ = ((data.q * caseA.a : ℕ) : ℝ) ^ 2
          * ∑ j : Fin k, (deg j : ℝ) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ((data.q * caseA.a : ℕ) : ℝ) ^ 2 * (2 * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * (data.q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
        rw [he]
        push_cast
        ring

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11) at the `A₀` level** — the two Clifford branches, before the descent to
`A(M)`.

`sOf_nineEleven_coherent` is this composed with `sOf_coherent_restrict`.  Both branches are run on
`A₀ = A ∪ V^M`: case (a) has no choice in the matter, since its (5.6) engine takes the Dade
hypothesis `h46.dade0` and its support facts therefore route through `(M')^# ⊆ A₀`, while
`(M')^# ⊆ A` is *false* for the type-uniform `A(M) = typePACore`.

This is also the level at which the §11/§13 packaging states (9.11)
(`S13.coherent_sOf_H0Cprime`): there `hyp.base.A0` is this support and `hyp.base.tau` is this map,
both definitionally (issue 1045, 着手順 3). -/
theorem sOf_nineEleven_coherent_A0 [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46.subH)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hdd : dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm)
    (h2 : ∀ caseA : CliffordCaseAData chars,
      2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))}.ncard)
    (hrefuteEq : ∀ caseA : CliffordCaseAData chars, CaseAEqualityRefutation caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (sOf data (chief.H0 ⊔ chars.Cprime))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) := by
  obtain ⟨η₁, hη₁⟩ := sOf_cprime_nonempty hG (chief := chief)
  rcases clifford_dichotomy hG chars with hA | hB
  · refine caseA_coherent_sOf_cprime_of_refuter hG chars _ _ hA.some
      (sOf_degreeSubfamily_coherent_A0
        (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) h46 dd hAnorm hdd htau
        hG hM data (chief.H0 ⊔ cprimeSub data chief) (data.q * hA.some.a)
        (hKeq.trans (huSub_eq_derivedInG_subgroupOf data)) hHle
        (Nat.cast_ne_zero.mpr (Nat.mul_pos data.nontrivial.2.1.pos hA.some.a_pos).ne')
        (h2 hA.some)
        (fun h => (OddOrder.Peterfalvi.S04.mem_sharp.mp
          (h46.dade.subset_sharp
            (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h))).2 rfl)).some
      (caseA_refuter_of_equality_refutation hG hA.some _ _
        (caseA_pairBound hG hM hA.some h46 hKeq htau hKsupp hVsub)
        (hrefuteEq hA.some))
  · exact caseB_coherent_sOf_cprime hG hM chars hB.some h46 hKeq htau hKsupp hVsub hη₁

end OddOrder.Peterfalvi.S11


