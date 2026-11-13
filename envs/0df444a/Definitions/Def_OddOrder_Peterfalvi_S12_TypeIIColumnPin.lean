-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIColumnPin
-- name    : OddOrder_Peterfalvi_S12_TypeIIColumnPin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:12:40.526942+00:00
-- url     : https://prove2.me/theorems/7d40778b-ee9d-49bb-a062-a97390a4651f
-- title:
--   Peterfalvi (5.8) for the type II column: the $\nu^{\tau_2}$ pin
-- statement:
--   Formalizes Peterfalvi (5.8) for the type II $S$-side column, pinning $\nu^{\tau_2}$ for the family $T_2=\{\lambda,\bar\lambda,\nu,\bar\nu\}$ of (10.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §5).
--
--   Main declarations: `typeII_T2_extension_columnSum_eq_sum` (Peterfalvi (5.5) for the reducible `T2`-column `ν = μ_{χ₂}`); `typeII_T2_extension_lam_eq_single` (Peterfalvi (5.5) for the irreducible `T2`-member `λ`); `typeII_dadeOfDiff_member_inner_chiFam_eq_zero` (The `R(λ)`-members are orthogonal to the whole `σ`-grid); `ticyclic_full_map_eq_induce` (The (3.1) `V`-TI Dade map is induction).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeIIColumnPin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeIIColumnPin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIFrobenius
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaTrichotomy

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

section ColumnPin

open OddOrder.BG.Ch3.S10

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the reducible `T2`-column `ν = μ_{χ₂}`** (mirror of the `M`-side
`Hypothesis.exists_muColumn_tau1_eq_sum_R`): the coherent extension of the (10.7) `T2`-family
sends `columnSum χ₂` to a subsum `∑_{α ∈ E} α` of its `R`-family `certainTypeR`, with
`|E| = ‖μ_{χ₂}‖² = w₁`.

Assembled from `CharacterPsiDecomposition.ofProjection` at `ψ = 0` (the `R`-family is the
landed `certainTypeR`; the lattice-relative isometry, `τ_S`-agreement on the `A₀(S)`-supported
`ν − ν̄`, and `ℤIrr`-membership are the `IsCoherent` fields; `⟨ν, ν̄⟩ = 0` is the cross-column
Gram entry) and `eq_sum_of_psi_eq_zero`. -/
theorem typeII_T2_extension_columnSum_eq_sum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    {χ₂ : ((typeIIHypothesis46 hG hSmax hSII data.typeP).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data.typeP).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data.typeP).W2)) →* ℂˣ}
    (hχ₂ne : χ₂ ≠ 1)
    (hkeq : nu = OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂) :
    ∃ E ⊆ (OddOrder.Peterfalvi.S06.certainTypeR
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm).imageSet,
      c.extension nu = ∑ α ∈ E, α ∧
        (E.card : ℂ) = (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1 : ℂ) := by
  classical
  subst hkeq
  -- membership and support bookkeeping for `ν, ν̄ ∈ T2` (`ν` is now the column sum)
  have hνT2 : OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
      ∈ ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
        : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hνcT2 : (OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj
      ∈ ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
        : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  -- `⟨ν, ν̄⟩ = 0`: the cross-column Gram entry `χ₂ ≠ χ₂⁻¹`
  have hχχbar : ClassFunction.inner
      (OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂)
      (OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj = 0 := by
    rw [OddOrder.Peterfalvi.S06.columnSum_conj_eq,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner,
      if_neg (OddOrder.Peterfalvi.S06.column_inv_ne_self
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne).symm]
  -- `ν − ν̄` is `ℤ[T2]` and `A₀(S)`-supported
  have hsuppmem : (OddOrder.Peterfalvi.S06.columnSum
        (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
      - (OddOrder.Peterfalvi.S06.columnSum
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
          : Set (ClassFunction ↥S ℂ))
        (OddOrder.Peterfalvi.S04.supportInSubgroup
          (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
            ∪ conjClassSetIn S (typePV S data.typeP)) S) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hνT2)
      (Submodule.subset_span hνcT2), ?_⟩
    refine (diff_support_subset_of_support_subset_union_one (hT2supp _ hνT2)
      (hT2supp _ hνcT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one _ hνcT2, hT2one _ hνT2]
  -- the lattice-relative isometry on `zSpan {ν − ν̄, ν − 0}`
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      {OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂
        - (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂ - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan
        ({lam, lam.conj,
          OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂,
          (OddOrder.Peterfalvi.S06.columnSum
            (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).conj}
          : Set (ClassFunction ↥S ℂ)) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hνT2)
        (Submodule.subset_span hνcT2)
    · rw [sub_zero]; exact Submodule.subset_span hνT2
  -- assemble the (5.4) decomposition and apply (5.5)
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      (OddOrder.Peterfalvi.S06.columnSum (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂) 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
      (OddOrder.Peterfalvi.S06.certainTypeR
        (typeIIHypothesis46 hG hSmax hSII data.typeP) hχ₂ne
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
          (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂).symm)
      c.extension
      (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (c.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact c.extension_mem_ZIrr _ (Submodule.subset_span hνT2))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  have hDt : D.tau1 = c.extension := rfl
  obtain ⟨-, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  rw [hDt] at hτ1
  refine ⟨E, hEsub, by rw [← hEsum]; exact hτ1, ?_⟩
  rw [hEcard, OddOrder.Peterfalvi.S06.columnSum_def,
    OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the irreducible `T2`-member `λ`**: the coherent extension sends `λ`
to a **single** signed Dade constituent — `λ^{τ₂} = α` for some `α ∈ R(λ)`
(`|E| = ‖λ‖² = 1`).  Same `ofProjection` assembly as the column case, with the 2-element Dade
`R(λ)` and `⟨λ, λ̄⟩ = 0` from distinctness of the conjugate pair (odd order). -/
theorem typeII_T2_extension_lam_eq_single [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)) :
    ∃ (hr : ¬ ClassFunction.IsReal lam)
      (hs : (lam.conj - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)
      (α : ClassFunction G ℂ),
      α ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        ⟨lam, hlam_irr⟩ hr hs).imageSet ∧
      c.extension lam = α := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  have hlamT2 : lam ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert _ _
  have hlamcT2 : lam.conj ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  have hlamIKF : lam ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG S).subgroupOf S) (Y.subgroupOf S) :=
    typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  -- realness and difference-support of `λ`
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hs : (lam.conj - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S := by
    refine (diff_support_subset_of_support_subset_union_one (hT2supp lam.conj hlamcT2)
      (hT2supp lam hlamT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one lam.conj hlamcT2, hT2one lam hlamT2]
  -- `⟨λ, λ̄⟩ = 0`: distinct irreducibles (`λ ≠ λ̄` in odd order)
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hχχbar : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  -- `λ − λ̄ ∈ ℤ[T2, A₀]` and the span bound
  have hsuppmem : (lam - lam.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hlamT2)
      (Submodule.subset_span hlamcT2), ?_⟩
    refine (diff_support_subset_of_support_subset_union_one (hT2supp lam hlamT2)
      (hT2supp lam.conj hlamcT2) ?_).trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
    rw [hT2one lam.conj hlamcT2, hT2one lam hlamT2]
  have hspan : OddOrder.Peterfalvi.S07.zSpan (L := ↥S) {lam - lam.conj, lam - 0}
      ≤ OddOrder.Peterfalvi.S07.zSpan
        ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.sub_mem _ (Submodule.subset_span hlamT2)
        (Submodule.subset_span hlamcT2)
    · rw [sub_zero]; exact Submodule.subset_span hlamT2
  -- assemble and apply (5.5); `|E| = ‖λ‖² = 1` forces a singleton
  let D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau) lam 0 :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        ⟨lam, hlam_irr⟩ hr hs)
      c.extension
      (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hspan hφ) (hspan hζ))
      (c.extends_on_supported _ hsuppmem)
      (by rw [sub_zero]; exact c.extension_mem_ZIrr lam (Submodule.subset_span hlamT2))
      (by rw [ClassFunction.inner_zero_right])
      (by rw [ClassFunction.inner_zero_right])
      hχχbar
  have hDt : D.tau1 = c.extension := rfl
  obtain ⟨-, hτ1, E, hEsub, hEsum, hEcard⟩ := D.eq_sum_of_psi_eq_zero
  rw [hDt] at hτ1
  have hlamnorm : ClassFunction.inner lam lam = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam, hlam_irr⟩
    rwa [if_pos rfl] at h
  have hE1 : E.card = 1 := by
    have : (E.card : ℂ) = 1 := by rw [hEcard, hlamnorm]
    exact_mod_cast this
  obtain ⟨α, hα⟩ := Finset.card_eq_one.mp hE1
  refine ⟨hr, hs, α, hEsub (by rw [hα]; exact Finset.mem_singleton_self α), ?_⟩
  rw [hτ1, hEsum, hα, Finset.sum_singleton]

set_option maxHeartbeats 800000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical FiniteInduce in
/-- **The `R(λ)`-members are orthogonal to the whole `σ`-grid** (Peterfalvi (5.3.b) for the
type-II `S`-side; standalone form of the key brick inside
`typeII_certainTypeR_imageSet_orthogonal_dadeOfDiff`, quantified over *every* grid column
`χ₂'`): each Dade constituent `β` of `(χ − χ̄)^{τ_S}` satisfies `⟨β, ω_{χ₂',i}^σ⟩ = 0`.

With the (5.5) singleton form `λ^{τ₂} ∈ R(λ)` this makes `λ^{τ₂}` orthogonal to the whole
grid — the input of the (3.2.e) `V`-vanishing of `λ^{τ₂}` in the (5.8) `ν`-pin. -/
theorem typeII_dadeOfDiff_member_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S) (data : TypePData S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data).W1)]
    (χ : IrreducibleCharacter ↥S)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥S ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S)
    (hdiffsuppχ : (((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data)) S)
    {β : ClassFunction G ℂ}
    (hβ : β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      χ hrealχ hdiffsuppχ).imageSet)
    (pq : (((OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data)).W1.subgroupOf
          (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W) →* ℂˣ)
      × (((OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data)).W2.subgroupOf
          (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W) →* ℂˣ)) :
    ClassFunction.inner β
      ((OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data)) pq) = 0 := by
  classical
  -- `hmin`: `2 < min(w₁, w₂)` for the `ticVdiff` exceptional structure.
  have hmin : 2 < min
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data)).three_le_card_W2
    omega
  -- core disjointness brick (as in the landed cross lemma)
  have key : ∀ {c c' : ℂ} {ξ ξ' : ClassFunction G ℂ},
      ξ ∈ ZIrr G → ClassFunction.inner ξ ξ = 1 → ξ' ∈ ZIrr G →
      ClassFunction.inner ξ' ξ' = 1 →
      ClassFunction.inner ξ ξ' = 0 → c ≠ 0 →
      (∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
        (c • ξ - c' • ξ') v = 0) →
      ClassFunction.inner (c • ξ)
        ((OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data)) pq) = 0 := by
    intro c c' ξ ξ' hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish
    exact OddOrder.Peterfalvi.S08.inner_smul_chiFam_eq_zero_of_diff_vanishOnV
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)) rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (typeIIHypothesis46 hG hSmax hSII data))
      hξZ hξ1 hξ'Z hξ'1 hξξ' hc hvanish hmin _
  -- `(χ − χ̄)^{τ_S}` vanishes on `V` (the type-II anchor)
  have hsuppsub : (((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj
      : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S := by
    rw [show (χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj =
        -((χ : ClassFunction ↥S ℂ).conj - (χ : ClassFunction ↥S ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  have htauvanish : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data).dade0 (typeIIHypothesis46 hG hSmax hSII data).tau
        ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data hsuppsub hv
  -- capture the two-element `R(χ)` abstractly and split the membership
  obtain ⟨cd, hcd⟩ :
      ∃ cd : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
          (typeIIHypothesis46 hG hSmax hSII data).dade0
          ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData))
        (χ : ClassFunction ↥S ℂ),
        OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
            (typeIIHypothesis46 hG hSmax hSII data).dade0 χ hrealχ hdiffsuppχ
          = cd.toOrthonormalImage := ⟨_, rfl⟩
  have hcdimg : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data).dade0
      ((typeIIHypothesis46 hG hSmax hSII data).dade0.fullDadeIsometryData)
      ((χ : ClassFunction ↥S ℂ) - (χ : ClassFunction ↥S ℂ).conj)
      = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction := by
    rw [cd.image_eq, smul_sub, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hμZ : cd.muClassFunction ∈ ZIrr G := cd.mu.mem_ZIrr
  have hνZ : cd.nuClassFunction ∈ ZIrr G := cd.nu.mem_ZIrr
  have hμ1 : ClassFunction.inner cd.muClassFunction cd.muClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.mu; rwa [if_pos rfl] at h
  have hν1 : ClassFunction.inner cd.nuClassFunction cd.nuClassFunction = 1 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.nu; rwa [if_pos rfl] at h
  have hμν : ClassFunction.inner cd.muClassFunction cd.nuClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.mu cd.nu; rwa [if_neg cd.distinct] at h
  have hνμ : ClassFunction.inner cd.nuClassFunction cd.muClassFunction = 0 := by
    have h := irreducibleCharacter_inner_eq_ite cd.nu cd.mu
    rwa [if_neg (Ne.symm cd.distinct)] at h
  have hsignC : (cd.sign : ℂ) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hnsignC : (-(cd.sign : ℂ)) ≠ 0 := by rcases cd.sign_eq with h | h <;> simp [h]
  have hvanishμν : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction) v = 0 := by
    intro v hv; rw [← hcdimg]; exact htauvanish v hv
  have hvanishνμ : ∀ v ∈
      (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data)).V,
      ((-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction) v = 0 := by
    intro v hv
    rw [show (-(cd.sign : ℂ)) • cd.nuClassFunction - (-(cd.sign : ℂ)) • cd.muClassFunction
        = (cd.sign : ℂ) • cd.muClassFunction - (cd.sign : ℂ) • cd.nuClassFunction by
      rw [neg_smul, neg_smul]; abel]
    exact hvanishμν v hv
  rw [hcd] at hβ
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage,
    Finset.mem_insert, Finset.mem_singleton] at hβ
  rcases hβ with rfl | rfl
  · rw [show cd.sign • cd.muClassFunction = (cd.sign : ℂ) • cd.muClassFunction from
      (Int.cast_smul_eq_zsmul ℂ cd.sign cd.muClassFunction).symm]
    exact key hμZ hμ1 hνZ hν1 hμν hsignC hvanishμν
  · rw [show (-cd.sign) • cd.nuClassFunction = (-(cd.sign : ℂ)) • cd.nuClassFunction by
      rw [← Int.cast_smul_eq_zsmul ℂ (-cd.sign) cd.nuClassFunction, Int.cast_neg]]
    exact key hνZ hν1 hμZ hμ1 hνμ hnsignC hvanishνμ

open scoped Classical FiniteInduce in
/-- **The (3.1) `V`-TI Dade map is induction**: on `CF(W, V)` the full Dade map of the
TI-cyclic hypothesis coincides with `Ind_W^G`.  Both are class functions supported on the
conjugates of `V` (`full_map_eq_zero_of_not_mem_conjugatesOfSet_V`; induction of a
`V`-supported function), and on `V` itself both evaluate to `α(v)` — the Dade map by the
base-point property (`full_map_eq_of_mem_V`), the induction because the TI property makes
every nonvanishing conjugator normalize into `W` (`V_ti` + `W_normalizes_V`), contributing
`|W|` equal terms against the `⅟|W|` normalization.

This is the bridge that turns the `σ`-adjunction into honest Frobenius reciprocity
(`ClassFunction.inner_induce_eq_inner_restrict`) in the (3.2.e) vanishing criterion. -/
theorem ticyclic_full_map_eq_induce [Finite G]
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp) :
    (app.tau.toDadeMap α : ClassFunction G ℂ)
      = ClassFunction.induce hyp.W (α : ClassFunction ↥hyp.W ℂ) := by
  classical
  -- values of `α` vanish off `V`
  have hαoff : ∀ (w : ↥hyp.W), (↑w : G) ∉ hyp.V → (α : ClassFunction ↥hyp.W ℂ) w = 0 := by
    intro w hw
    by_contra hne
    exact hw (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
      ((ClassFunction.mem_supportedSubmodule.mp α.2) (ClassFunction.mem_support.mpr hne)))
  ext g
  by_cases hg : g ∈ Group.conjugatesOfSet hyp.V
  · -- both sides are class functions; evaluate at the `V`-representative
    obtain ⟨v, hv, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    rw [← (app.tau.toDadeMap α : ClassFunction G ℂ).of_isConj hconj,
      ← (ClassFunction.induce hyp.W (α : ClassFunction ↥hyp.W ℂ)).of_isConj hconj,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_of_mem_V app α hv,
      ClassFunction.induce_apply]
    -- the conjugators with `x⁻¹vx ∈ W` are exactly `x ∈ W`, each contributing `α(v)`
    have hterm : ∀ x : G, ClassFunction.induceTerm hyp.W (α : ClassFunction ↥hyp.W ℂ) x v
        = if x ∈ hyp.W then (α : ClassFunction ↥hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ else 0 := by
      intro x
      by_cases hxW : x ∈ hyp.W
      · have hxv : x⁻¹ * v * x ∈ hyp.V := by
          have := hyp.W_normalizes_V (⟨x, hxW⟩ : ↥hyp.W)⁻¹ hv
          simpa using this
        have hxvW : x⁻¹ * v * x ∈ hyp.W := hyp.V_subset_W hxv
        rw [ClassFunction.induceTerm_of_mem _ hxvW, if_pos hxW]
        -- `x⁻¹vx` is `W`-conjugate to `v`
        exact (α : ClassFunction ↥hyp.W ℂ).of_isConj (isConj_iff.mpr
          ⟨(⟨x, hxW⟩ : ↥hyp.W)⁻¹, Subtype.ext (by simp [mul_assoc])⟩) |>.symm
      · rw [if_neg hxW]
        by_cases hxvW : x⁻¹ * v * x ∈ hyp.W
        · rw [ClassFunction.induceTerm_of_mem _ hxvW]
          refine hαoff _ (fun hxvV => hxW ?_)
          have := hyp.V_ti x⁻¹ ⟨v, hv, by simpa using hxvV⟩
          simpa using this
        · exact ClassFunction.induceTerm_of_not_mem _ hxvW
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero]
    have hcard : (Finset.univ.filter (fun x : G => x ∈ hyp.W)).card
        = Nat.card ↥hyp.W := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]
  · rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.full_map_eq_zero_of_not_mem_conjugatesOfSet_V
      app α hg, ClassFunction.induce_apply]
    have hterm : ∀ x : G, ClassFunction.induceTerm hyp.W (α : ClassFunction ↥hyp.W ℂ) x g = 0 := by
      intro x
      by_cases hxgW : x⁻¹ * g * x ∈ hyp.W
      · rw [ClassFunction.induceTerm_of_mem _ hxgW]
        refine hαoff _ (fun hxgV => hg ?_)
        refine Group.mem_conjugatesOfSet_iff.mpr ⟨x⁻¹ * g * x, hxgV, ?_⟩
        exact isConj_iff.mpr ⟨x, by group⟩
      · exact ClassFunction.induceTerm_of_not_mem _ hxgW
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero, mul_zero]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (3.2)(e)**: a class function of `G` orthogonal to the whole `σ`-image family
`{χ_{pq}}` vanishes on `V` (Coq `ortho_cycTIiso_vanish`).

Frobenius reciprocity (`inner_induce_eq_inner_restrict`) through the `σ = Ind` bridge
(`ticyclic_full_map_eq_induce`) turns the grid-orthogonality of `ψ` into the
`α_{pq}`-orthogonality of `Res_W ψ` (each `σ(α_{pq})` is a four-term `χ`-combination by
`alphaCF_eq_omega_combination` + `sigma_omega`); the `(1.3)(a)`-engine
`vanishOnV_of_inner_alphaCF` then forces `(Res_W ψ)|_V = 0`, i.e. `ψ|_V = 0`.

Together with the (5.5) singleton `λ^{τ₂} ∈ R(λ)` and the grid-orthogonality of the
`R(λ)`-members (`typeII_dadeOfDiff_member_inner_omegaSigma_eq_zero`) this gives the
`V`-vanishing of `λ^{τ₂}` in the (5.8) `ν`-pin. -/
theorem ticyclic_apply_eq_zero_of_forall_inner_chiFam [Finite G]
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp)
    {ψ : ClassFunction G ℂ}
    (h : ∀ pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      ClassFunction.inner ψ (hyp.chiFam hVeq app pq) = 0)
    {v : G} (hv : v ∈ hyp.V) : ψ v = 0 := by
  classical
  -- flipped-order grid orthogonality
  have hχ0 : ∀ pq, ClassFunction.inner (hyp.chiFam hVeq app pq) ψ = 0 := fun pq => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h pq, star_zero]
  -- `Res_W ψ ⊥ α_{pq}` via reciprocity through `σ = Ind`
  have hf : ∀ (p : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (q : (hyp.W2.subgroupOf hyp.W) →* ℂˣ),
      p ≠ 1 → q ≠ 1 →
      ClassFunction.inner (hyp.alphaCF p q) (ClassFunction.restrict hyp.W ψ) = 0 := by
    intro p q _ _
    rw [← ClassFunction.inner_induce_eq_inner_restrict hyp.W (hyp.alphaCF p q) ψ]
    have hbridge : ClassFunction.induce hyp.W (hyp.alphaCF p q)
        = hyp.sigma hVeq app (hyp.alphaCF p q) := by
      rw [show hyp.alphaCF p q
          = ((hyp.alpha hVeq p q : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ hyp)
            : ClassFunction ↥hyp.W ℂ) from rfl,
        ← ticyclic_full_map_eq_induce hyp app (hyp.alpha hVeq p q),
        OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_eq_tau]
    rw [hbridge, OddOrder.Peterfalvi.S05.TICyclicHypothesis.alphaCF_eq_omega_combination,
      map_add, map_sub, map_sub,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_omega,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_omega,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_omega,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_omega]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_sub_left, hχ0,
      sub_zero, add_zero]
  have hres := OddOrder.Peterfalvi.S05.TICyclicHypothesis.vanishOnV_of_inner_alphaCF hyp hVeq
    hf hv
  rwa [ClassFunction.restrict_apply] at hres

open scoped Classical FiniteInduce in
/-- **`λ^{τ₂}` vanishes on the exceptional set `V`** (the first half of the `V`-vanishing
transfer): by (5.5) `λ^{τ₂}` is a single `R(λ)`-constituent, each of which is orthogonal to
the whole `σ`-image family (`typeII_dadeOfDiff_member_inner_chiFam_eq_zero`); the (3.2)(e)
criterion (`ticyclic_apply_eq_zero_of_forall_inner_chiFam`) then kills its `V`-values. -/
theorem typeII_T2_extension_lam_apply_eq_zero_of_mem_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).V) :
    c.extension lam v = 0 := by
  classical
  obtain ⟨hr, hs, α, hαmem, hα⟩ := typeII_T2_extension_lam_eq_single hG hSmax hSII data
    hlam_mem hlam_irr hnu_mem hdeg c
  -- the `A(S)`-level support of the conjugate difference (the cross lemma's anchor input)
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  have hlamT2 : lam ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert _ _
  have hlamcT2 : lam.conj ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hsA : (lam.conj - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
    diff_support_subset_of_support_subset_union_one (hT2supp lam.conj hlamcT2)
      (hT2supp lam hlamT2)
      (by rw [hT2one lam.conj hlamcT2, hT2one lam hlamT2])
  refine ticyclic_apply_eq_zero_of_forall_inner_chiFam
    (OddOrder.Peterfalvi.S06.ticVdiff (typeIIHypothesis46 hG hSmax hSII data.typeP)) rfl
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
      (typeIIHypothesis46 hG hSmax hSII data.typeP))
    (fun pq => ?_) hv
  rw [hα]
  exact typeII_dadeOfDiff_member_inner_chiFam_eq_zero hG hSmax hSII data.typeP
    ⟨lam, hlam_irr⟩ hr hsA hs hαmem pq

open scoped Classical FiniteInduce in
/-- **`ν^{τ₂}` vanishes on the exceptional set `V`**: since `λ` and `ν` share a degree, the
difference `ν − λ` is `A(S)`-supported, so `τ₂(ν − λ) = τ_S(ν − λ)` (coherence agreement)
vanishes on `V` by the (8.16) base-point anchor; with `λ^{τ₂}|_V = 0`
(`typeII_T2_extension_lam_apply_eq_zero_of_mem_V`) this transfers to `ν^{τ₂}`.  (The
equal-degree situation makes Coq's scaled `zeta1 = ζ(1)·μ − μ(1)·ζ` unnecessary.) -/
theorem typeII_T2_extension_nu_apply_eq_zero_of_mem_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).V) :
    c.extension nu v = 0 := by
  classical
  have hT2supp := typeII_T2_member_support hG hSmax hSII data hlam_mem hnu_mem
  have hT2one := typeII_T2_apply_one_eq data hlam_mem hnu_mem hdeg
  have hlamT2 : lam ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert _ _
  have hνT2 : nu ∈ ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  -- `ν − λ` is `A(S)`-supported (equal degrees) and lies in `ℤ[T2]`
  have hnulamsupp : ((nu - lam : ClassFunction ↥S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)) S :=
    diff_support_subset_of_support_subset_union_one (hT2supp nu hνT2) (hT2supp lam hlamT2)
      (by rw [hT2one nu hνT2, hT2one lam hlamT2])
  have hz1span : (nu - lam) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S) :=
    ⟨Submodule.sub_mem _ (Submodule.subset_span hνT2) (Submodule.subset_span hlamT2),
      hnulamsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)⟩
  -- `τ₂(ν − λ) = τ_S(ν − λ)` vanishes at `v` (base-point anchor)
  have hagree := c.extends_on_supported _ hz1span
  have hτv := typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data.typeP hnulamsupp hv
  have hdiffv : c.extension (nu - lam) v = 0 := by rw [hagree]; exact hτv
  have hlamv := typeII_T2_extension_lam_apply_eq_zero_of_mem_V hG hSmax hSII data
    hlam_mem hlam_irr hnu_mem hdeg c hv
  have hexp : c.extension (nu - lam) v = c.extension nu v - c.extension lam v := by
    rw [map_sub]
    rfl
  rw [hexp, hlamv, sub_zero] at hdiffv
  exact hdiffv

section IndexComponents

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
/-- The bridge image of a `tic`-side `W₂`-part element lies in the `sdiff`-side `W₂`-part
(underlying `G`-elements agree, `coe_ticWEquivSdiffW`, and `tic.W₂` is the `L`-image of
`W₂`, `tic_W2`). -/
theorem ticWEquivSdiffW_mem_W2 [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {g : h.tic.W} (hg : (g : G) ∈ h.tic.W2) :
    OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g
      ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf]
  have hwG : (((OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g) : ↥L) : G) = (g : G) :=
    OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW h g
  rw [h.tic_W2] at hg
  obtain ⟨y, hy, hyeq⟩ := hg
  have hLeq : ((OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g) : ↥L) = y :=
    Subtype.ext (by rw [hwG, ← hyeq]; rfl)
  rw [hLeq]
  exact hy

open scoped Classical in
/-- `W₁`-part companion of `ticWEquivSdiffW_mem_W2`. -/
theorem ticWEquivSdiffW_mem_W1 [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {g : h.tic.W} (hg : (g : G) ∈ h.tic.W1) :
    OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g
      ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W := by
  rw [Subgroup.mem_subgroupOf]
  have hwG : (((OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g) : ↥L) : G) = (g : G) :=
    OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW h g
  rw [h.tic_W1] at hg
  obtain ⟨y, hy, hyeq⟩ := hg
  have hLeq : ((OddOrder.Peterfalvi.S06.ticWEquivSdiffW h g) : ↥L) = y :=
    Subtype.ext (by rw [hwG, ← hyeq]; rfl)
  rw [hLeq]
  exact hy

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **The `σ`-grid index of `ω_{χ₂,i}` has `W₂`-component independent of the row `i`**: the
second component of `omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)` — the restriction of the
transported product character to the `W₂`-part — sees only the `χ₂`-factor
(`chiColumn_apply_of_mem_W2`).  This is the "column" well-definedness behind the two-column
σ-coefficient support of `ν^{τ₂}` in the (5.8) endgame. -/
theorem omegaProdCharTic_symm_snd_eq [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i i' : Fin (Nat.card h.W1)) :
    ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂ i)).2
    = ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂ i')).2 := by
  classical
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv_symm_eq,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv_symm_eq]
  refine MonoidHom.ext fun w => Units.ext ?_
  simp only [MonoidHom.comp_apply]
  have hmem : OddOrder.Peterfalvi.S06.ticWEquivSdiffW h
      (((OddOrder.Peterfalvi.S06.ticVdiff h).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff h).W).subtype w)
      ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
    ticWEquivSdiffW_mem_W2 h (Subgroup.mem_subgroupOf.mp w.2)
  erw [OddOrder.Peterfalvi.S06.omegaProdCharTic_apply,
    OddOrder.Peterfalvi.S06.omegaProdCharTic_apply,
    OddOrder.Peterfalvi.S06.chiColumn_apply_of_mem_W2 h χ₂ i hmem,
    OddOrder.Peterfalvi.S06.chiColumn_apply_of_mem_W2 h χ₂ i' hmem]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **The `σ`-grid index of `ω_{χ₂,i}` has `W₁`-component independent of the column `χ₂`**:
the first component sees only the row factor (`chiColumn_apply_of_mem_W1`). -/
theorem omegaProdCharTic_symm_fst_eq [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂ i)).1
    = ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂' i)).1 := by
  classical
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv_symm_eq,
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdEquiv_symm_eq]
  refine MonoidHom.ext fun w => Units.ext ?_
  simp only [MonoidHom.comp_apply]
  have hmem : OddOrder.Peterfalvi.S06.ticWEquivSdiffW h
      (((OddOrder.Peterfalvi.S06.ticVdiff h).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff h).W).subtype w)
      ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
    ticWEquivSdiffW_mem_W1 h (Subgroup.mem_subgroupOf.mp w.2)
  erw [OddOrder.Peterfalvi.S06.omegaProdCharTic_apply,
    OddOrder.Peterfalvi.S06.omegaProdCharTic_apply,
    OddOrder.Peterfalvi.S06.chiColumn_apply_of_mem_W1 h.toCore χ₂ i hmem,
    OddOrder.Peterfalvi.S06.chiColumn_apply_of_mem_W1 h.toCore χ₂' i hmem]

open scoped Classical in
/-- **Distinct columns give distinct `W₂`-components**: for `χ₂ ≠ χ₂'`, the second components
of the transported grid indices differ (the full pairs differ by
`omegaProdEquiv_symm_omegaProdCharTic_ne` while the first components agree by
`omegaProdCharTic_symm_fst_eq`).  Supplies the `jcol ≠ kcol` hypothesis of the (5.8)
endgame. -/
theorem omegaProdCharTic_symm_snd_ne [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (i : Fin (Nat.card h.W1)) :
    ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂ i)).2
    ≠ ((OddOrder.Peterfalvi.S06.ticVdiff h).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic h χ₂' i)).2 := by
  intro heq
  refine OddOrder.Peterfalvi.S06.omegaProdEquiv_symm_omegaProdCharTic_ne h hne i ?_
  exact Prod.ext (omegaProdCharTic_symm_fst_eq h χ₂ χ₂' i) heq

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (5.8), the `μ`-column dichotomy at Hypothesis (4.6) generality.**

Let `ψ` be a sum over a sub-family `E ⊆ R(μ_j)` of the (4.9) column image family, with
`|E| = w₁`, and suppose `ψ` vanishes on the exceptional set `V`.  Then `ψ` is a **signed full
`σ`-grid column**:

`ψ = δ_j·∑_p χ_{(p, kcol)}`  or  `ψ = −δ_j·∑_p χ_{(p, jcol)}`

where `δ_j = (columnFamily χ₂).sign` and `kcol`/`jcol` are the `W₂`-components of the `χ₂`/`χ₂⁻¹`
grid indices.  This is the book's (5.8) conclusion: the two hypotheses `hEsum`/`hEcard` are its
(5.5) input (`μ_k^{τ₁}` is a norm-`w₁` sub-sum of `R(μ_k)`) and `hψV` is its `V`-vanishing step,
which the book derives from (5.3.b) + (4.7) — both now available abstractly (issue 0159).

Assembly through the S05 `σ`-coefficient endgame `eq_smul_chiFam_column_of_vanishOnV`: the subsum
reindexed along the injective `certainTypeRImage`, the two-column `{0, ±δ}` coefficient grid (grid
orthonormality + `omegaProdCharTic_symm_snd_eq`/`_ne`), the norm `‖ψ‖² = w₁` and Parseval.

The FT instances supply the two hypotheses by their own routes; `typeII_nu_tau2_dichotomy` is the
type-II one (issue 0161). -/
theorem certainTypeR_subsum_dichotomy [Fintype G] [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A L) [NeZero (Nat.card h46.W1)]
    [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [Fintype (↥((OddOrder.Peterfalvi.S06.ticVdiff h46).W1.subgroupOf
      (OddOrder.Peterfalvi.S06.ticVdiff h46).W) →* ℂˣ)]
    [Finite (↥((OddOrder.Peterfalvi.S06.ticVdiff h46).W2.subgroupOf
      (OddOrder.Peterfalvi.S06.ticVdiff h46).W) →* ℂˣ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hne1 : χ₂ ≠ 1)
    {ψ : ClassFunction G ℂ} {E : Finset (ClassFunction G ℂ)}
    (hEsub : E ⊆ (OddOrder.Peterfalvi.S06.certainTypeR h46 hne1
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet)
    (hEsum : ψ = ∑ α ∈ E, α)
    (hEcard : (E.card : ℂ) = (Nat.card h46.W1 : ℂ))
    (hψV : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, ψ v = 0)
    (i₀ : Fin (Nat.card h46.W1)) :
    ψ
        = ((h46.columnFamily χ₂).sign : ℂ)
          • ∑ p, (OddOrder.Peterfalvi.S06.ticVdiff
              h46).chiFam rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              h46)
            (p, ((OddOrder.Peterfalvi.S06.ticVdiff
                h46).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                h46 χ₂ i₀)).2) ∨
      ψ
        = (-((h46.columnFamily χ₂).sign : ℂ))
          • ∑ p, (OddOrder.Peterfalvi.S06.ticVdiff
              h46).chiFam rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              h46)
            (p, ((OddOrder.Peterfalvi.S06.ticVdiff
                h46).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                h46 χ₂⁻¹ i₀)).2) := by
  have : Fintype (↥((OddOrder.Peterfalvi.S06.ticVdiff h46).W2.subgroupOf
      (OddOrder.Peterfalvi.S06.ticVdiff h46).W) →* ℂˣ) := Fintype.ofFinite _
  classical
  -- shorthands (plain `have`-free abbreviations via local notation would not fold; spell out)
  set δ : ℂ := ((h46.columnFamily χ₂).sign : ℂ)
    with hδdef
  have hδpm : δ = 1 ∨ δ = -1 := by
    rcases (h46.columnFamily χ₂).sign_eq with h | h
    · left; rw [hδdef, h]; norm_num
    · right; rw [hδdef, h]; norm_num
  have hδstar : star δ = δ := by rcases hδpm with h | h <;> rw [h] <;> norm_num
  have hδsq : δ * δ = 1 := by rcases hδpm with h | h <;> rw [h] <;> norm_num
  have hsstar : ∀ b : Bool, star (cond b (-δ) δ) = cond b (-δ) δ := by
    intro b; cases b
    · exact hδstar
    · change star (-δ) = -δ
      rw [star_neg, hδstar]
  have hssq : ∀ b : Bool, (cond b (-δ) δ) * (cond b (-δ) δ) = 1 := by
    intro b; cases b
    · exact hδsq
    · change (-δ) * (-δ) = 1
      rw [neg_mul_neg]; exact hδsq
  have hχinv : χ₂⁻¹ ≠ χ₂ := OddOrder.Peterfalvi.S06.column_inv_ne_self
    h46 hne1
  -- reindex the (5.5) subsum along the injective `R`-family (the `muColumn_tau1_pin` pattern)
  have hRinj : Function.Injective (OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹) :=
    OddOrder.Peterfalvi.S06.certainTypeRImage_injective _ hχinv.symm
  have hEsub' : E ⊆ Finset.univ.image (OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹) := hEsub
  set T : Finset (Bool × Fin (Nat.card h46.W1)) :=
    Finset.univ.filter (fun x => OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹ x ∈ E) with hTdef
  have hImT : T.image (OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹) = E := by
    apply Finset.ext; intro α
    simp only [Finset.mem_image, hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hα
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hEsub' hα)
      exact ⟨x, by rw [hx]; exact hα, hx⟩
  have hSumT : ∑ x ∈ T, OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹ x = ∑ α ∈ E, α := by
    rw [← hImT, Finset.sum_image (fun x _ y _ h => hRinj h)]
  have hCardT : (T.card : ℂ)
      = (Nat.card h46.W1 : ℂ) := by
    have hc : (T.image (OddOrder.Peterfalvi.S06.certainTypeRImage
        h46 χ₂ χ₂⁻¹)).card = E.card := by
      rw [hImT]
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hRinj h)] at hc
    rw [hc]; exact hEcard
  have hXT : ψ = ∑ x ∈ T, OddOrder.Peterfalvi.S06.certainTypeRImage
      h46 χ₂ χ₂⁻¹ x := by
    rw [hEsum, hSumT]
  -- the grid-index map and the `chiFam`-form of the `R`-members
  have hRP : ∀ x : Bool × Fin (Nat.card h46.W1),
      OddOrder.Peterfalvi.S06.certainTypeRImage
        h46 χ₂ χ₂⁻¹ x
      = (cond x.1 (-δ) δ) • (OddOrder.Peterfalvi.S06.ticVdiff
          h46).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff
            h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 (cond x.1 χ₂⁻¹ χ₂) x.2)) := by
    rintro ⟨b, i⟩
    cases b
    · change OddOrder.Peterfalvi.S06.certainTypeRImage _ χ₂ χ₂⁻¹ (false, i) = δ • _
      simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
      rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam, hδdef]
      rfl
    · change OddOrder.Peterfalvi.S06.certainTypeRImage _ χ₂ χ₂⁻¹ (true, i) = (-δ) • _
      simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
      rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam, hδdef]
      rfl
  -- σ-coefficient formula
  have hcoeff : ∀ pq, (OddOrder.Peterfalvi.S06.ticVdiff
      h46).sigmaCoeff rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        h46) (ψ) pq
      = ∑ x ∈ T, (cond x.1 (-δ) δ)
        * (if (OddOrder.Peterfalvi.S06.ticVdiff
            h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 (cond x.1 χ₂⁻¹ χ₂) x.2) = pq
          then (1 : ℂ) else 0) := by
    intro pq
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff, hXT,
      OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hRP x, ClassFunction.inner_smul_left,
      ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).chiFam_spec rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46)).2.2.1]
  -- the two columns and their separation
  have hsndF : ∀ i, ((OddOrder.Peterfalvi.S06.ticVdiff
      h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂ i)).2
      = ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂ i₀)).2 := fun i =>
    omegaProdCharTic_symm_snd_eq h46 χ₂ i i₀
  have hsndT : ∀ i, ((OddOrder.Peterfalvi.S06.ticVdiff
      h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂⁻¹ i)).2
      = ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂⁻¹ i₀)).2 := fun i =>
    omegaProdCharTic_symm_snd_eq h46 χ₂⁻¹ i i₀
  have hkj : ((OddOrder.Peterfalvi.S06.ticVdiff
      h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂⁻¹ i₀)).2
      ≠ ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
      (OddOrder.Peterfalvi.S06.omegaProdCharTic
        h46 χ₂ i₀)).2 :=
    omegaProdCharTic_symm_snd_ne h46 hχinv i₀
  -- per-column row-injectivity of the grid-index map (via the injective `R`-family)
  have hPinjF : ∀ i i' : Fin (Nat.card h46.W1),
      ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂ i))
      = ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂ i')) → i = i' := by
    intro i i' hP
    have hReq : OddOrder.Peterfalvi.S06.certainTypeRImage
        h46 χ₂ χ₂⁻¹ (false, i)
        = OddOrder.Peterfalvi.S06.certainTypeRImage
          h46 χ₂ χ₂⁻¹ (false, i') := by
      rw [hRP (false, i), hRP (false, i')]
      exact congrArg _ (congrArg _ hP)
    have := hRinj hReq
    exact (Prod.ext_iff.mp this).2
  have hPinjT : ∀ i i' : Fin (Nat.card h46.W1),
      ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂⁻¹ i))
      = ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂⁻¹ i')) → i = i' := by
    intro i i' hP
    have hReq : OddOrder.Peterfalvi.S06.certainTypeRImage
        h46 χ₂ χ₂⁻¹ (true, i)
        = OddOrder.Peterfalvi.S06.certainTypeRImage
          h46 χ₂ χ₂⁻¹ (true, i') := by
      rw [hRP (true, i), hRP (true, i')]
      exact congrArg _ (congrArg _ hP)
    have := hRinj hReq
    exact (Prod.ext_iff.mp this).2
  -- full injectivity of the (cond-indexed) grid-index map on `Bool × Fin w₁`
  have hPinj : ∀ x y : Bool × Fin (Nat.card h46.W1),
      ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 (cond x.1 χ₂⁻¹ χ₂) x.2))
      = ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 (cond y.1 χ₂⁻¹ χ₂) y.2)) → x = y := by
    rintro ⟨b, i⟩ ⟨b', i'⟩ hP
    cases b <;> cases b'
    · exact Prod.ext rfl (hPinjF i i' hP)
    · exact absurd ((hsndF i).symm.trans ((congrArg Prod.snd hP).trans (hsndT i'))) (Ne.symm hkj)
    · exact absurd ((hsndT i).symm.trans ((congrArg Prod.snd hP).trans (hsndF i'))) hkj
    · exact Prod.ext rfl (hPinjT i i' hP)
  -- the endgame inputs
  have hsupp : ∀ pq, pq.2 ≠ ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂⁻¹ i₀)).2 →
      pq.2 ≠ ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 χ₂ i₀)).2 →
      (OddOrder.Peterfalvi.S06.ticVdiff
        h46).sigmaCoeff rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46) (ψ) pq = 0 := by
    intro pq hpj hpk
    rw [hcoeff]
    refine Finset.sum_eq_zero fun x hx => ?_
    rcases x with ⟨b, i⟩
    cases b
    · dsimp only
      rw [show (bif false then χ₂⁻¹ else χ₂) = χ₂ from rfl,
        if_neg (fun hP => hpk (((congrArg Prod.snd hP).symm.trans (hsndF i)) : pq.2 = _)),
        mul_zero]
    · dsimp only
      rw [show (bif true then χ₂⁻¹ else χ₂) = χ₂⁻¹ from rfl,
        if_neg (fun hP => hpj (((congrArg Prod.snd hP).symm.trans (hsndT i)) : pq.2 = _)),
        mul_zero]
  have hk : ∀ p, (OddOrder.Peterfalvi.S06.ticVdiff
        h46).sigmaCoeff rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46) (ψ)
        (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂ i₀)).2) = 0 ∨
      (OddOrder.Peterfalvi.S06.ticVdiff
        h46).sigmaCoeff rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46) (ψ)
        (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂ i₀)).2) = δ := by
    intro p
    rw [hcoeff]
    by_cases hex : ∃ x ∈ T, ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 (cond x.1 χ₂⁻¹ χ₂) x.2))
        = (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂ i₀)).2)
    · obtain ⟨x₁, hx₁T, hx₁P⟩ := hex
      -- `x₁` is a `false`-index (a `true`-hit would equate `jcol = kcol`)
      have hx₁b : x₁.1 = false := by
        rcases x₁ with ⟨b, i⟩
        cases b
        · rfl
        · exact absurd (((hsndT i).symm.trans (congrArg Prod.snd hx₁P)) :
            _ = _) hkj
      right
      rw [Finset.sum_eq_single x₁ (fun y hyT hyne => by
        rw [if_neg (fun hP => hyne (hPinj y x₁ (hP.trans hx₁P.symm))), mul_zero])
        (fun h => absurd hx₁T h), if_pos hx₁P]
      rcases x₁ with ⟨b, i⟩
      cases b
      · change δ * 1 = δ
        rw [mul_one]
      · exact absurd hx₁b (by simp)
    · left
      refine Finset.sum_eq_zero fun y hyT => ?_
      rw [if_neg (fun hP => hex ⟨y, hyT, hP⟩), mul_zero]
  have hj : ∀ p, (OddOrder.Peterfalvi.S06.ticVdiff
        h46).sigmaCoeff rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46) (ψ)
        (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂⁻¹ i₀)).2) = 0 ∨
      (OddOrder.Peterfalvi.S06.ticVdiff
        h46).sigmaCoeff rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          h46) (ψ)
        (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂⁻¹ i₀)).2) = -δ := by
    intro p
    rw [hcoeff]
    by_cases hex : ∃ x ∈ T, ((OddOrder.Peterfalvi.S06.ticVdiff
        h46).omegaProdEquiv.symm
        (OddOrder.Peterfalvi.S06.omegaProdCharTic
          h46 (cond x.1 χ₂⁻¹ χ₂) x.2))
        = (p, ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).omegaProdEquiv.symm
          (OddOrder.Peterfalvi.S06.omegaProdCharTic
            h46 χ₂⁻¹ i₀)).2)
    · obtain ⟨x₁, hx₁T, hx₁P⟩ := hex
      have hx₁b : x₁.1 = true := by
        rcases x₁ with ⟨b, i⟩
        cases b
        · exact absurd (((hsndF i).symm.trans (congrArg Prod.snd hx₁P)) :
            _ = _) (Ne.symm hkj)
        · rfl
      right
      rw [Finset.sum_eq_single x₁ (fun y hyT hyne => by
        rw [if_neg (fun hP => hyne (hPinj y x₁ (hP.trans hx₁P.symm))), mul_zero])
        (fun h => absurd hx₁T h), if_pos hx₁P]
      rcases x₁ with ⟨b, i⟩
      cases b
      · exact absurd hx₁b (by simp)
      · change (-δ) * 1 = -δ
        rw [mul_one]
    · left
      refine Finset.sum_eq_zero fun y hyT => ?_
      rw [if_neg (fun hP => hex ⟨y, hyT, hP⟩), mul_zero]
  -- norm and Parseval
  have hcardW1 : (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff
      h46).W1 : ℂ)
      = (Nat.card h46.W1 : ℂ) := by
    congr 1
    rw [show (OddOrder.Peterfalvi.S06.ticVdiff
        h46).W1
      = h46.tic.W1 from rfl,
      h46.tic_W1]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ L.subtype_injective).toEquiv).symm
  have hXnorm : ClassFunction.inner (ψ) (ψ)
      = (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff
        h46).W1 : ℂ) := by
    rw [hcardW1, hEsum, OddOrder.RepresentationTheory.inner_self_sum_orthonormal_eq_card
      (fun a ha b hb => (OddOrder.Peterfalvi.S06.certainTypeR h46 hne1
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).orthonormal
        a (hEsub ha) b (hEsub hb))]
    exact hEcard
  have hParseval : ClassFunction.inner (ψ) (ψ)
      = ∑ pq, (OddOrder.Peterfalvi.S06.ticVdiff
          h46).sigmaCoeff rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            h46) (ψ) pq
        * star ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).sigmaCoeff rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            h46) (ψ) pq) := by
    have hRHS : ∑ pq, (OddOrder.Peterfalvi.S06.ticVdiff
          h46).sigmaCoeff rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            h46) (ψ) pq
        * star ((OddOrder.Peterfalvi.S06.ticVdiff
          h46).sigmaCoeff rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            h46) (ψ) pq)
        = (T.card : ℂ) := by
      have hterm : ∀ pq, (OddOrder.Peterfalvi.S06.ticVdiff
            h46).sigmaCoeff rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              h46) (ψ) pq
          * star ((OddOrder.Peterfalvi.S06.ticVdiff
            h46).sigmaCoeff rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              h46) (ψ) pq)
          = ∑ x ∈ T, ∑ y ∈ T, ((cond x.1 (-δ) δ) * (cond y.1 (-δ) δ))
            * ((if (OddOrder.Peterfalvi.S06.ticVdiff
                h46).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                h46 (cond x.1 χ₂⁻¹ χ₂) x.2) = pq
              then (1 : ℂ) else 0)
            * (if (OddOrder.Peterfalvi.S06.ticVdiff
                h46).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                h46 (cond y.1 χ₂⁻¹ χ₂) y.2) = pq
              then (1 : ℂ) else 0)) := by
        intro pq
        rw [hcoeff, star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        have hsy : star ((cond y.1 (-δ) δ) * (if (OddOrder.Peterfalvi.S06.ticVdiff
            h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond y.1 χ₂⁻¹ χ₂) y.2) = pq
            then (1 : ℂ) else 0))
            = (cond y.1 (-δ) δ) * (if (OddOrder.Peterfalvi.S06.ticVdiff
            h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond y.1 χ₂⁻¹ χ₂) y.2) = pq
            then (1 : ℂ) else 0) := by
          rw [star_mul', hsstar y.1]
          congr 1
          split
          · exact star_one ℂ
          · exact star_zero ℂ
        rw [hsy]
        ring
      rw [Finset.sum_congr rfl fun pq _ => hterm pq]
      rw [Finset.sum_comm]
      have hinner : ∀ x ∈ T, ∑ y ∈ T, ∑ pq, ((cond x.1 (-δ) δ) * (cond y.1 (-δ) δ))
          * ((if (OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond x.1 χ₂⁻¹ χ₂) x.2) = pq
            then (1 : ℂ) else 0)
          * (if (OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond y.1 χ₂⁻¹ χ₂) y.2) = pq
            then (1 : ℂ) else 0)) = 1 := by
        intro x hxT
        rw [Finset.sum_eq_single x (fun y hyT hyne => ?_) (fun h => absurd hxT h)]
        · -- diagonal `y = x`: the `pq`-sum hits exactly `pq = P x`
          rw [Finset.sum_eq_single (((OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond x.1 χ₂⁻¹ χ₂) x.2)))
            (fun pq _ hpqne => by rw [if_neg (fun hh => hpqne hh.symm), mul_zero, mul_zero])
            (fun h => absurd (Finset.mem_univ _) h)]
          rw [if_pos rfl, mul_one, mul_one, hssq]
        · -- off-diagonal: `P y ≠ P x` kills every `pq`
          refine Finset.sum_eq_zero fun pq _ => ?_
          by_cases hx : ((OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond x.1 χ₂⁻¹ χ₂) x.2)) = pq
          · rw [if_pos hx, if_neg (fun hy => hyne (hPinj y x (hy.trans hx.symm))),
              mul_zero, mul_zero]
          · rw [if_neg hx, zero_mul, mul_zero]
      have hstep : ∀ x ∈ T, (∑ pq, ∑ y ∈ T, ((cond x.1 (-δ) δ) * (cond y.1 (-δ) δ))
          * ((if (OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond x.1 χ₂⁻¹ χ₂) x.2) = pq
            then (1 : ℂ) else 0)
          * (if (OddOrder.Peterfalvi.S06.ticVdiff
              h46).omegaProdEquiv.symm
            (OddOrder.Peterfalvi.S06.omegaProdCharTic
              h46 (cond y.1 χ₂⁻¹ χ₂) y.2) = pq
            then (1 : ℂ) else 0))) = 1 := by
        intro x hx
        rw [Finset.sum_comm]
        exact hinner x hx
      rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hRHS, hXnorm, hcardW1, ← hCardT]
  -- fire the S05 endgame
  rcases (OddOrder.Peterfalvi.S06.ticVdiff
      h46).eq_smul_chiFam_column_of_vanishOnV rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        h46) hψV hkj hsupp hδpm hk hj hXnorm
      hParseval with hcase | hcase
  · left; rw [hδdef] at hcase; exact hcase
  · right; rw [hδdef] at hcase; exact hcase

end IndexComponents

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.8) for the type-II `S`-side column — the `ν^{τ₂}` dichotomy** (Coq
`coherent_prDade_TIred`): the coherent image of the reducible `T2`-column
`ν = μ_{χ₂} = columnSum χ₂` is a **signed full `σ`-grid column**.

The type-II instance of `certainTypeR_subsum_dichotomy` (issue 0161): the abstract theorem's two
inputs are supplied here by `typeII_T2_extension_columnSum_eq_sum` (the (5.5) norm-`w₁` subsum)
and `typeII_T2_extension_nu_apply_eq_zero_of_mem_V` (the `V`-vanishing). -/
theorem typeII_nu_tau2_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    {χ₂ : ((typeIIHypothesis46 hG hSmax hSII data.typeP).W2.subgroupOf
        ((typeIIHypothesis46 hG hSmax hSII data.typeP).W1
          ⊔ (typeIIHypothesis46 hG hSmax hSII data.typeP).W2)) →* ℂˣ}
    (hne1 : χ₂ ≠ 1)
    (hkeq : nu = OddOrder.Peterfalvi.S06.columnSum
      (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂)
    (i₀ : Fin (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)) :
    c.extension nu
        = (((typeIIHypothesis46 hG hSmax hSII data.typeP).columnFamily χ₂).sign : ℂ)
          • ∑ p, (OddOrder.Peterfalvi.S06.ticVdiff
              (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              (typeIIHypothesis46 hG hSmax hSII data.typeP))
            (p, ((OddOrder.Peterfalvi.S06.ticVdiff
                (typeIIHypothesis46 hG hSmax hSII data.typeP)).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂ i₀)).2) ∨
      c.extension nu
        = (-(((typeIIHypothesis46 hG hSmax hSII data.typeP).columnFamily χ₂).sign : ℂ))
          • ∑ p, (OddOrder.Peterfalvi.S06.ticVdiff
              (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
            (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
              (typeIIHypothesis46 hG hSmax hSII data.typeP))
            (p, ((OddOrder.Peterfalvi.S06.ticVdiff
                (typeIIHypothesis46 hG hSmax hSII data.typeP)).omegaProdEquiv.symm
              (OddOrder.Peterfalvi.S06.omegaProdCharTic
                (typeIIHypothesis46 hG hSmax hSII data.typeP) χ₂⁻¹ i₀)).2) := by
  obtain ⟨E, hEsub, hEsum, hEcard⟩ := typeII_T2_extension_columnSum_eq_sum hG hSmax hSII data
    hlam_mem hnu_mem hdeg c hne1 hkeq
  exact certainTypeR_subsum_dichotomy (typeIIHypothesis46 hG hSmax hSII data.typeP) hne1
    hEsub hEsum hEcard
    (fun v hv => typeII_T2_extension_nu_apply_eq_zero_of_mem_V hG hSmax hSII data hlam_mem
      hlam_irr hnu_mem hdeg c hv) i₀

end ColumnPin

end OddOrder.Peterfalvi.S12


