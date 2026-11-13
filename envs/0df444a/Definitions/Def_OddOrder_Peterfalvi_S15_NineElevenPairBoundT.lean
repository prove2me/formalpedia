-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenPairBoundT
-- name    : OddOrder_Peterfalvi_S15_NineElevenPairBoundT
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:55.909659+00:00
-- url     : https://prove2.me/theorems/83bf982e-e387-42b8-8648-5eee7d040285
-- title:
--   Peterfalvi (9.11.1) at $T$: the (5.6) pair-bound world
-- statement:
--   The $T$-side mirror of the $S$-instance (9.11) pair-bound development (Peterfalvi, pp. 87-91), including the identification of the $T$-instance family with its $H_0C'$ stratum.
--
--   Main declarations: `Hypothesis.sSet_eq_sOf_H0Cprime_T` (The honest `T`-instance family is its own `H₀C′` stratum); `Hypothesis.uprimeSub_eq_bot_T` (`U′ = [U, U] = ⊥` for the type-`P₂` maximal `T`); `Hypothesis.sOf_H0_uprime_eq_sSet_T` (`𝒮(H₀ ⊔ U′) = 𝒯`); `Hypothesis.sSet_subset_inducedKernelFamily_T` (`𝒯 = sSet(setupT)` embeds into the general kernel-filter family `S(⊥)`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_NineElevenPairBoundT.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_NineElevenPairBoundT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_TSetMemberRFamily

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
/-- **The honest `T`-instance family is its own `H₀C′` stratum**: `𝒯 = sSet(setupT) = 𝒮(H₀C′)`
(mirror of `sSet_eq_sOf_H0Cprime`, the linchpin bridging the `sSet` refuter to the generic
(9.11) `sOf`-stratum machinery).  For the type-`P₂` maximal `T` the kernel data degenerates —
`chief.H₀ = ⊥` (`toTypesIIIIIIVSetupT_chief_H0_eq_bot`) and `C′ = cprimeSub = derivedInG (cSub)
= ⊥` (`cSub ≤ V` abelian by the unconditional `isMulCommutative_V_unconditional`) — so
`chief.H₀ ⊔ chars.Cprime = ⊥` and `𝒮(H₀C′) = 𝒮(⊥) = 𝒯`. -/
theorem Hypothesis.sSet_eq_sOf_H0Cprime_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief) :
    sSet (hyp.toTypesIIIIIIVSetupT hG hvd)
      = sOf (hyp.toTypesIIIIIIVSetupT hG hvd) (chief.H0 ⊔ chars.Cprime) := by
  classical
  have hH0 : chief.H0 = ⊥ := hyp.toTypesIIIIIIVSetupT_chief_H0_eq_bot hG hvd chief
  have hCp : chars.Cprime = ⊥ := by
    change OddOrder.Peterfalvi.S11.cprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief = ⊥
    have hCV : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief
        ≤ hyp.V :=
      (OddOrder.Peterfalvi.S11.cSub_le_U _ _).trans
        (le_of_eq (hyp.toTypesIIIIIIVSetupT_U_eq hG hvd))
    have hVab : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
    have hCab : IsMulCommutative
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) :=
      ⟨⟨fun a b => Subtype.ext (by
        have h := hVab.is_comm.comm
          (⟨(a : G), hCV a.2⟩ : ↥hyp.V) ⟨(b : G), hCV b.2⟩
        simpa using congrArg Subtype.val h)⟩⟩
    have hcomm : commutator
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hCab.is_comm.comm a b
    change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) = ⊥
    rw [derivedInG, hcomm, Subgroup.map_bot]
  rw [hH0, hCp, sup_bot_eq, sOf_bot_eq_sSet]

open OddOrder.Peterfalvi.S11 in
/-- **`U′ = [U, U] = ⊥` for the type-`P₂` maximal `T`** (mirror of `uprimeSub_eq_bot`;
Peterfalvi (13.2.a) at `T`: abelian `V`).  `setupT.U = V` is abelian
(`isMulCommutative_V_unconditional`), so its derived subgroup vanishes. -/
theorem Hypothesis.uprimeSub_eq_bot_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd) = ⊥ := by
  change derivedInG (hyp.toTypesIIIIIIVSetupT hG hvd).U = ⊥
  have hUV : (hyp.toTypesIIIIIIVSetupT hG hvd).U ≤ hyp.V :=
    le_of_eq (hyp.toTypesIIIIIIVSetupT_U_eq hG hvd)
  have hVab : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
  have hUab : IsMulCommutative ↥(hyp.toTypesIIIIIIVSetupT hG hvd).U :=
    ⟨⟨fun a b => Subtype.ext (by
      have h := hVab.is_comm.comm
        (⟨(a : G), hUV a.2⟩ : ↥hyp.V) ⟨(b : G), hUV b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hcomm : commutator ↥(hyp.toTypesIIIIIIVSetupT hG hvd).U = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hUab.is_comm.comm a b
  rw [derivedInG, hcomm, Subgroup.map_bot]

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮(H₀ ⊔ U′) = 𝒯`** for the type-`P₂` `T`-instance (mirror of `sOf_H0_uprime_eq_sSet`,
the strata-collapse bridge): the generic (9.11) anchor stratum equals the full family. -/
theorem Hypothesis.sOf_H0_uprime_eq_sSet_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd))
      = sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := by
  rw [hyp.toTypesIIIIIIVSetupT_chief_H0_eq_bot hG hvd chief, hyp.uprimeSub_eq_bot_T hG hvd,
    sup_bot_eq, sOf_bot_eq_sSet]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`𝒯 = sSet(setupT)` embeds into the general kernel-filter family `S(⊥)`** (mirror of
`sSet_subset_inducedKernelFamily`).  Every member `η = Ind_{HU}^T ξ` (`ξ ∈ 𝒳`, hence `ξ`
nontrivial) lies in `S(⊥) = inducedKernelFamily ((derivedInG T).subgroupOf T) ⊥`, the
membership the general §8 family layer consumes. -/
theorem Hypothesis.sSet_subset_inducedKernelFamily_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    sSet (hyp.toTypesIIIIIIVSetupT hG hvd) ⊆
      OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.T).subgroupOf hyp.T) (⊥ : Subgroup ↥hyp.T) := by
  have := hyp.finiteG
  rintro η ⟨ξ, hξ, rfl⟩
  have hξne : ξ ≠ trivialIrreducibleCharacter
      ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) := by
    intro htriv
    apply hξ
    rw [htriv]
    simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hmemHU : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        (huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) (⊥ : Subgroup ↥hyp.T) := by
    refine ⟨ξ, hξne, ?_, (induceHU_eq_induce (hyp.toTypesIIIIIIVSetupT hG hvd) _)⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx)
      rw [Subgroup.mem_bot] at h2; exact Subtype.ext h2
    rw [hx1]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hKeq : huSub (hyp.toTypesIIIIIIVSetupT hG hvd)
      = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf _
  exact hKeq ▸ hmemHU

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Scaled-difference support for `𝒯`-members** (mirror of `sSet_scaledDiff_support`, the
honest-`A(T)` analogue of `inducedKernelFamily_scaledDiff_support`).  For members
`φ, ψ ∈ 𝒯` with a matching scaled degree `φ(1) = c·ψ(1)`, the difference `φ − c·ψ` vanishes
at `1`, so its support lands in `A(T)` (`sSet_member_support_subset_T`). -/
theorem Hypothesis.sSet_scaledDiff_support_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ ψ : ClassFunction ↥hyp.T ℂ}
    (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hψ : ψ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    {c : ℕ}
    (hdeg : (φ : ↥hyp.T → ℂ) 1 = (c : ℂ) * (ψ : ↥hyp.T → ℂ) 1) :
    (φ - c • ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  have hnsmul : ∀ y : ↥hyp.T, (c • ψ : ClassFunction ↥hyp.T ℂ) y = (c : ℂ) * ψ y := fun y => by
    rw [← Nat.cast_smul_eq_nsmul ℂ c ψ, ClassFunction.smul_apply]
  have hzero : (φ - c • ψ) (1 : ↥hyp.T) = 0 := by
    rw [ClassFunction.sub_apply, hnsmul, hdeg, sub_self]
  have hcψsupp : (c • ψ : ClassFunction ↥hyp.T ℂ).support ⊆ ψ.support := by
    intro w hw
    rw [ClassFunction.mem_support] at hw ⊢
    intro hwψ
    apply hw
    rw [hnsmul, hwψ, mul_zero]
  intro z hz
  have hz0 : (φ - c • ψ) z ≠ 0 := hz
  rcases ClassFunction.support_sub_subset φ (c • ψ) hz with h | h
  · rcases hyp.sSet_member_support_subset_T hG hvd hφ h with h' | h'
    · exact h'
    · rw [Set.mem_singleton_iff] at h'; subst h'; exact absurd hzero hz0
  · rcases hyp.sSet_member_support_subset_T hG hvd hψ (hcψsupp h) with h' | h'
    · exact h'
    · rw [Set.mem_singleton_iff] at h'; subst h'; exact absurd hzero hz0

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Per-member (5.4) decomposition `D(φ)` for a member `φ ∈ 𝒮₂`, case-agnostic** (mirror of
`sSet_memberPsiDecomp`).  The `ψ = 0` `CharacterPsiDecomposition` over the honest `T`-Dade map
whose orthonormal image family is the case-agnostic `R`-family `sSet_memberRFamily_T` and whose
auxiliary isometry is the coherent extension `ν = hS₂coh.extension`. -/
noncomputable def Hypothesis.sSet_memberPsiDecomp_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {S₂ : Set (ClassFunction ↥hyp.T ℂ)}
    (hS₂coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData))
      S₂ (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {φ : ClassFunction ↥hyp.T ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hφS₂ : φ ∈ S₂) (hφcS₂ : (φ : ClassFunction ↥hyp.T ℂ).conj ∈ S₂) :
    { D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥hyp.T) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData)) φ 0 //
      D.imageFamily = hyp.sSet_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hφ ∧
      D.tau1 φ = hS₂coh.extension φ } := by
  classical
  haveI := hyp.finiteG
  have hφmem : φ ∈ Submodule.span ℤ S₂ := Submodule.subset_span hφS₂
  have hφcmem : (φ : ClassFunction ↥hyp.T ℂ).conj ∈ Submodule.span ℤ S₂ :=
    Submodule.subset_span hφcS₂
  have hdiffsupp : ((φ : ClassFunction ↥hyp.T ℂ).conj - φ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T :=
    hyp.sSet_member_conjDiff_supported_T hG hvd hφ
  have hfam : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG hyp.T).subgroupOf hyp.T) (⊥ : Subgroup ↥hyp.T) :=
    hyp.sSet_subset_inducedKernelFamily_T hG hvd hφ
  have hχχbar : ClassFunction.inner φ (φ : ClassFunction ↥hyp.T ℂ).conj = 0 := by
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hfam
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hfam) (fun h => ?_)
    exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hφ h.symm
  have hνZ : hS₂coh.extension φ ∈ ZIrr G := hS₂coh.extension_mem_ZIrr φ hφmem
  have hle : Submodule.span ℤ ({φ - (φ : ClassFunction ↥hyp.T ℂ).conj, φ - 0}
      : Set (ClassFunction ↥hyp.T ℂ)) ≤ Submodule.span ℤ S₂ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hφmem hφcmem
    · rw [sub_zero]; exact hφmem
  have hdiffsupported : (φ - (φ : ClassFunction ↥hyp.T ℂ).conj) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ hφmem hφcmem, by
        rw [show (φ - (φ : ClassFunction ↥hyp.T ℂ).conj)
            = -((φ : ClassFunction ↥hyp.T ℂ).conj - φ) from by abel,
          ClassFunction.support_neg]
        exact hdiffsupp⟩
  exact ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.sSet_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hφ) hS₂coh.extension
    (fun ψ' ζ' hψ' hζ' => hS₂coh.extension_inner_eq ψ' ζ' (hle hψ') (hle hζ'))
    (hS₂coh.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp) (by simp) hχχbar, rfl, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The break decomposition `Da` for a pair-refuted member `χ`, case-agnostic** (mirror of
`sSet_breakPsiDecomp`).  The `ψ = a·χ₁` `CharacterPsiDecomposition` over the honest `T`-Dade
map (with `τ` itself as the auxiliary isometry, so `Da.tau1 = τ`) whose image family is the
case-agnostic `R`-family; the difference set `{χ − χ̄, χ − a·χ₁}` is `A(T)`-supported, so the
Dade isometry preserves the sponsoring-lattice inner products. -/
noncomputable def Hypothesis.sSet_breakPsiDecomp_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {χ : ClassFunction ↥hyp.T ℂ} (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    {χ₁ : ClassFunction ↥hyp.T ℂ} {a : ℕ}
    (hdiffasupp : (χ - a • χ₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)
    (htau1_mema : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
        (χ - a • χ₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner χ (a • χ₁ : ClassFunction ↥hyp.T ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥hyp.T ℂ).conj
      (a • χ₁ : ClassFunction ↥hyp.T ℂ) = 0)
    (hχχbar : ClassFunction.inner χ (χ : ClassFunction ↥hyp.T ℂ).conj = 0) :
    { Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥hyp.T) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData)) χ (a • χ₁) //
      Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) ∧
      Da.imageFamily = hyp.sSet_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hχ } := by
  classical
  haveI := hyp.finiteG
  have hdiffsupp : ((χ : ClassFunction ↥hyp.T ℂ).conj - χ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T :=
    hyp.sSet_member_conjDiff_supported_T hG hvd hχ
  have hSdiff : ∀ s ∈ ({χ - (χ : ClassFunction ↥hyp.T ℂ).conj, χ - a • χ₁}
      : Set (ClassFunction ↥hyp.T ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ - (χ : ClassFunction ↥hyp.T ℂ).conj)
          = -((χ : ClassFunction ↥hyp.T ℂ).conj - χ) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  exact ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.sSet_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hχ)
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
      ((hyp.dadeHypT hG hTP).fullDadeIsometryData))
    (fun ψ' ζ' hψ' hζ' =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        (hyp.dadeHypT hG hTP) hSdiff hψ' hζ')
    rfl htau1_mema hχaχ1 hχbaraχ1 hχχbar, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1), the `T`-instance (5.6) pair-bound residual** (mirror of
`nineElevenPairBoundS`, issue 2035 refuter-`T` campaign; the M-side provider
`S11.nineElevenPairBound` requires `htype : IsTypeIII M ∨ IsTypeIV M` — false for the type-II
`T` — so it is rebuilt in the `indT`/`A(T)` world).  For a pair-refuted `χ ∈ 𝒯 ∖ 𝒮₂` (its
conjugate pair `{χ, χ̄}` not coherently adjoinable to the coherent maximal `𝒮₂`), the member
`χ = Ind_{HU}^T ζ` has degree `χ(1) = setupT.q·d` with source degree `d ≤ u`, and every finite
`F ⊆ 𝒮₂` obeys the (5.6) norm-weighted degree-square bound `sumnS F ≤ 2·setupT.q²·a·d`
(Theorem (5.6) at the degree-`setupT.q·a` anchor read contrapositively through
`S08.coherentDegreeSqNormBound_of_not_coherentW_k`). -/
theorem Hypothesis.nineElevenPairBoundT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.T ℂ))
    (hS₁S₂ : hyp.sSetIrrDegT hG hvd (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (χ : ClassFunction ↥hyp.T ℂ)
    (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂)
    (hnopair : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT (S₂ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))) :
    ∃ d : ℕ, ((χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * d : ℕ) : ℂ)) ∧
      d ≤ chars.u ∧
      ∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
        OddOrder.Peterfalvi.S07.sumnS F
          ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
  classical
  have := hyp.finiteG
  obtain ⟨hχS, hχnotS₂⟩ := hχ
  obtain ⟨cohS₂_indT⟩ := hS₂coh
  -- (1) Dade-side coherence via `congrMap`: `indT = Ind_T^G = τ` on `A(T)`-supported class
  -- functions.
  have hindT_dade : ∀ f : ClassFunction ↥hyp.T ℂ,
      f ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) →
      hyp.indT f = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) f := fun f hf => by
    rw [hyp.indT_apply, ← hyp.tInstance_dade_eq_induce hG hnoV hTP
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2]
  have cohS₂ := cohS₂_indT.congrMap hindT_dade
  -- (2) not-coherent (Dade side) from `hnopair` (indT side), the contrapositive of `congrMap`.
  have hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData))
      (S₂ ∪ {χ, χ.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) := by
    rintro ⟨c⟩
    refine hnopair ⟨c.congrMap (fun f hf => ?_)⟩
    rw [hyp.tInstance_dade_eq_induce hG hnoV hTP
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2, hyp.indT_apply]
  -- (3) break dictionary: `χ = Ind_{HU}^T ξ`, `χ(1) = q·d`, `d ≤ u`, source ratio `q·a·e`.
  have hχsOf : χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ chars.Cprime) := by rw [← hyp.sSet_eq_sOf_H0Cprime_T hG hvd chars]; exact hχS
  obtain ⟨ξ, hξ, rfl⟩ := OddOrder.Peterfalvi.S11.mem_sOf.mp hχsOf
  obtain ⟨d, -, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  have hχdeg : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * d : ℕ) : ℂ) := by
    rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdζ]; push_cast; ring
  have hduC := OddOrder.Peterfalvi.S11.xiOf_H0Cprime_source_apply_one_le_u chars hξ
  rw [hdζ] at hduC
  have hdu : d ≤ chars.u := by
    have h := (Complex.le_def.mp hduC).1
    rw [Complex.natCast_re, Complex.natCast_re] at h
    exact_mod_cast h
  obtain ⟨e, he⟩ := OddOrder.Peterfalvi.S11.caseA_sOf_source_degree_ratio caseA
    (OddOrder.Peterfalvi.S11.mem_sOf.mpr ⟨ξ, hξ, rfl⟩)
  have hde : d = caseA.a * e := by
    have h1 : (hyp.toTypesIIIIIIVSetupT hG hvd).q * d
        = (hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a * e := by exact_mod_cast hχdeg.symm.trans he
    have h2 : (hyp.toTypesIIIIIIVSetupT hG hvd).q * d
        = (hyp.toTypesIIIIIIVSetupT hG hvd).q * (caseA.a * e) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos h2
  -- (4) anchor: a degree-`qa` irreducible of `𝒮`, transported into `𝒮₂` via `hS₁S₂`.
  obtain ⟨χ₁, hχ₁sOfU', hχ₁irr, hχ₁deg⟩ :=
    OddOrder.Peterfalvi.S11.caseA_exists_irreducible_qa hG chars caseA
  have hχ₁sSet : χ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := by
    have h1 : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) := by
      rw [OddOrder.Peterfalvi.S11.Section11CharacterData.SOf_eq] at hχ₁sOfU'; exact hχ₁sOfU'
    rwa [hyp.sOf_H0_uprime_eq_sSet_T hG hvd chief] at h1
  have hχ₁S₂ : χ₁ ∈ S₂ := hS₁S₂ ⟨hχ₁sSet, hχ₁irr, hχ₁deg⟩
  -- (5) `S₂` is finite; enumerate it and locate the anchor index.
  have hS₂fin : S₂.Finite := (sSet_finite (hyp.toTypesIIIIIIVSetupT hG hvd)).subset hS₂S
  obtain ⟨k, χmem, hinj, hrange⟩ := OddOrder.Peterfalvi.S08.exists_finEnum_general hS₂fin
  have hmemS1set : ∀ j, χmem j ∈ S₂ := fun j => hrange ▸ Set.mem_range_self j
  have hχ₁mem : χ₁ ∈ Set.range χmem := hrange ▸ hχ₁S₂
  obtain ⟨i₁, hi₁eq⟩ := hχ₁mem
  subst hi₁eq
  have hmemsSet : ∀ j, χmem j ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    fun j => hS₂S (hmemS1set j)
  have hmemsOf : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ chars.Cprime) := fun j => by
    rw [← hyp.sSet_eq_sOf_H0Cprime_T hG hvd chars]; exact hmemsSet j
  choose deg hdeg using fun j : Fin k =>
    OddOrder.Peterfalvi.S11.caseA_sOf_source_degree_ratio caseA (hmemsOf j)
  have hdeg_anchor : ∀ j, (χmem j : ↥hyp.T → ℂ) 1
      = (deg j : ℂ) * (χmem i₁ : ↥hyp.T → ℂ) 1 := by
    intro j; rw [hdeg j, hχ₁deg]; push_cast; ring
  have ha1 : deg i₁ = 1 := by
    have h : (hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a * 1
        = (hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a * deg i₁ := by
      rw [mul_one]; exact Nat.cast_inj.mp (hχ₁deg.symm.trans (hdeg i₁))
    exact (Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos caseA.a_pos) h).symm
  have hψdeg : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        : ↥hyp.T → ℂ) 1 = (e : ℂ) * (χmem i₁ : ↥hyp.T → ℂ) 1 := by
    rw [hχdeg, hχ₁deg, hde]; push_cast; ring
  -- (6) family-layer facts via the `S(⊥)` embedding: Gram data, break-character orthogonalities.
  have hχfam : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.T).subgroupOf hyp.T) (⊥ : Subgroup ↥hyp.T) :=
    hyp.sSet_subset_inducedKernelFamily_T hG hvd hχS
  have hmemfam : ∀ j, χmem j ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG hyp.T).subgroupOf hyp.T) (⊥ : Subgroup ↥hyp.T) :=
    fun j => hyp.sSet_subset_inducedKernelFamily_T hG hvd (hmemsSet j)
  have hmcpos : ∀ j, 0 < (ClassFunction.inner (χmem j) (χmem j)).re := fun j =>
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam j)).2
  have hmemortho : ∀ i j, ClassFunction.inner (χmem i) (χmem j)
      = @ite ℂ (i = j) (Classical.propDecidable (i = j))
          (((ClassFunction.inner (χmem i) (χmem i)).re : ℝ) : ℂ) 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]
      exact (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hmemfam i)).1
    · rw [if_neg hij]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hmemfam i) (hmemfam j) (fun h => hij (hinj h))
  have hχcnotS₂ : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)).conj
        ∉ S₂ := by
    intro hc; apply hχnotS₂
    have h := hS₂conj hc; rwa [ClassFunction.conj_conj] at h
  have hdiffsuppχ : ((OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      - OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T :=
    hyp.sSet_member_conjDiff_supported_T hG hvd hχS
  have hχψb : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hχfam
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hχfam)
      (fun h =>
        sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hχS h.symm)
  have hχbψ : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hχfam) hχfam
      (fun h => sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hχS h)
  have hχχne : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      ≠ 0 := by
    rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hχfam).1]
    exact_mod_cast (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hχfam).2.ne'
  have hχbχbne : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      ≠ 0 := by
    have hcf := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate
      (⊥ : Subgroup ↥hyp.T) hχfam
    rw [(OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hcf).1]
    exact_mod_cast (OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos hcf).2.ne'
  have hψ_S1 : ∀ x ∈ S₂, ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)) x
      = 0 := fun x hx =>
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) hχS (hS₂S hx)
      (fun h => hχnotS₂ (h ▸ hx))
  have hψbar_S1 : ∀ x ∈ S₂, ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj x
      = 0 := fun x hx =>
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd)
      (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hχS) (hS₂S hx)
      (fun h => hχcnotS₂ (h ▸ hx))
  -- (7) scaled-difference supports (honest `A(T)`), `ZIrr`-integrality, generation clauses.
  have hmemdegdiffsupp : ∀ i : Fin k, i ∈ (Finset.univ : Finset (Fin k)) →
      ((χmem i - deg i • χmem i₁).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) := fun i _ =>
    hyp.sSet_scaledDiff_support_T hG hvd (hmemsSet i) (hmemsSet i₁) (hdeg_anchor i)
  have hdiffasuppχ : (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      - e • χmem i₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T :=
    hyp.sSet_scaledDiff_support_T hG hvd hχS (hmemsSet i₁) hψdeg
  have htau1ψ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
      ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        - e • χmem i₁) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported (hyp.dadeHypT hG
        hTP) hdiffasuppχ
      (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hχfam)
        (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hmemfam i₁)) e))
  have hcover : ∀ x ∈ S₂, ∃ j, j ∈ (Finset.univ : Finset (Fin k)) ∧ χmem j = x := by
    intro x hx; rw [← hrange] at hx; obtain ⟨j, hj⟩ := hx; exact ⟨j, Finset.mem_univ j, hj⟩
  have hSgen :=
    OddOrder.Peterfalvi.S07.span_subset_span_zSupportedSpan_union_anchor_of_scaledDiffs
      (s := (Finset.univ : Finset (Fin k))) (χmem := χmem) (deg := deg) (i₁ := i₁)
      hcover (Finset.mem_univ i₁) (fun j _ => hmemS1set j) hmemdegdiffsupp
  have hbar1 : ((OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
        : ↥hyp.T → ℂ) 1
      = (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        : ↥hyp.T → ℂ) 1 := by
    rw [ClassFunction.conj_apply, hχdeg]; exact star_natCast _
  have hχ₁ne : (χmem i₁ : ↥hyp.T → ℂ) 1 ≠ 0 := by
    rw [hχ₁deg]
    exact Nat.cast_ne_zero.mpr
      (Nat.mul_pos (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos caseA.a_pos).ne'
  have h1A : (1 : ↥hyp.T)
      ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simp
  have hgen :=
    OddOrder.Peterfalvi.S07.zSupportedSpan_adjoinPair_subset_span_of_anchorGeneration
      (χ := OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      (chibar := (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj)
      (chi1 := χmem i₁) (a := e)
      hSgen hψdeg hbar1 hχ₁ne h1A
  -- (8) the decomposition supply from the case-agnostic `R`-family (break `Da`, per-member `D`).
  have hχaeχ1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
      (e • χmem i₁ : ClassFunction ↥hyp.T ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ e (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hψ_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  have hχbaraeχ1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          ℂ)).conj
      (e • χmem i₁ : ClassFunction ↥hyp.T ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ e (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hψbar_S1 (χmem i₁) (hmemS1set i₁), mul_zero]
  obtain ⟨Da, hDatau1, hDaimg⟩ :=
    hyp.sSet_breakPsiDecomp_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hχS hdiffasuppχ htau1ψ
      hχaeχ1 hχbaraeχ1 hχψb
  have memberDatum := fun j : Fin k =>
    hyp.sSet_memberPsiDecomp_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 cohS₂ (hmemsSet j)
      (hmemS1set j) (hS₂conj (hmemS1set j))
  have hortho_mem : ∀ i (_ : i ∈ (Finset.univ : Finset (Fin k))),
      ((memberDatum i).1).imageFamily.Orthogonal Da.imageFamily := by
    intro i _
    rw [(memberDatum i).2.1, hDaimg]
    exact hyp.sSet_memberRFamily_orthogonal_T hG hnoV pins hvd hTP Tdata hU hW1 hW2
      (hmemsSet i) hχS
      (sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) (hmemsSet i) hχS
        (fun h => hχnotS₂ (h ▸ hmemS1set i)))
      (sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) (hmemsSet i)
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hχS)
        (fun h => hχcnotS₂ (h ▸ hmemS1set i)))
  -- (9) fire the norm-weighted (5.6) engine (contrapositive of `xAdjoinStepW_k`).
  have hbound := OddOrder.Peterfalvi.S08.coherentDegreeSqNormBound_of_not_coherentW_k
    (hyp.dadeHypT hG hTP) cohS₂
    (OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ))
    hdiffsuppχ hχχne hχbχbne hχψb hχbψ hψ_S1 hψbar_S1
    (Finset.univ : Finset (Fin k)) χmem deg i₁ (Finset.mem_univ i₁)
    hmemdegdiffsupp (fun j _ => hmemS1set j)
    (fun j => (ClassFunction.inner (χmem j) (χmem j)).re) (fun j _ => hmcpos j)
    (fun i _ j _ => hmemortho i j)
    (fun i _ => (memberDatum i).1)
    Da hDatau1 hortho_mem (fun i _ => (memberDatum i).2.2)
    hdiffasuppχ htau1ψ ha1 hSgen hgen hnc
  -- (10) rescale `sumnS F ≤ sumnS 𝒮₂ = (setupT.q·a)²·∑ deg²/‖·‖² ≤ (qa)²·2e = 2q²a·d`.
  refine ⟨d, hχdeg, hdu, ?_⟩
  intro F hF
  have hFsub : F ⊆ hS₂fin.toFinset := fun ψ hψ => hS₂fin.mem_toFinset.mpr (hF hψ)
  have henum : OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset
      = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := by
    rw [OddOrder.Peterfalvi.S07.sumnS,
      show hS₂fin.toFinset = (Set.range χmem).toFinset by
        ext ψ; rw [Set.Finite.mem_toFinset, Set.mem_toFinset, hrange],
      OddOrder.Peterfalvi.S08.sum_toFinset_range_eq hinj]
  have hsnorm : ∀ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j)
      = ((deg j : ℝ) * (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ)) ^ 2
        / (ClassFunction.inner (χmem j) (χmem j)).re := by
    intro j
    unfold OddOrder.Peterfalvi.S07.Snorm
    congr 1
    rw [hdeg j, Complex.natCast_re]; push_cast; ring
  calc OddOrder.Peterfalvi.S07.sumnS F
      ≤ OddOrder.Peterfalvi.S07.sumnS hS₂fin.toFinset :=
        OddOrder.Peterfalvi.S07.sumnS_le_of_subset hFsub
    _ = ∑ j : Fin k, OddOrder.Peterfalvi.S07.Snorm (χmem j) := henum
    _ = ∑ j : Fin k, ((deg j : ℝ) * (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ)) ^ 2
          / (ClassFunction.inner (χmem j) (χmem j)).re :=
        Finset.sum_congr rfl (fun j _ => hsnorm j)
    _ = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ) ^ 2
          * ∑ j : Fin k, (deg j : ℝ) ^ 2 / (ClassFunction.inner (χmem j) (χmem j)).re := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ) ^ 2 * (2 * (e : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) := by
        rw [hde]; push_cast; ring

end OddOrder.Peterfalvi.S15


