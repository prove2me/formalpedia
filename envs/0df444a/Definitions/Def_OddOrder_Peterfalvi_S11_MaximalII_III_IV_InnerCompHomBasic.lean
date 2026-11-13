-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:02:54.495206+00:00
-- url     : https://prove2.me/theorems/23bbee40-cd97-41e5-b79a-1d35cc51c8da
-- title:
--   Peterfalvi §11: the inner-complement homomorphism, opening layer
-- statement:
--   The opening layer of the inner-complement homomorphism development. It proves the case (b) exhaustion of $\mathcal{X}(H_0C)$ by inductions and the core of Peterfalvi (13.3.a) (`isIndHC`).
--
--   Main declarations: `caseB_xiOf_H0C_eq_induce_hcPsi` (Case-(b) exhaustion of `𝒳(H₀C)` by `hcPsi`-inductions); `isIndHC_of_source_eq_induce_hcPsi` (Stages-flattening); `caseB_reducible_sOf_H0_isIndHC` (Peterfalvi (13.3.a) core (Coq `PFsection9.isIndHC`)).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
set_option backward.isDefEq.respectTransparency false in
/-- **Case-(b) exhaustion of `𝒳(H₀C)` by `hcPsi`-inductions** (Clifford correspondence, the
surjectivity half of the case-(b) `oXtheta`): every `χ ∈ 𝒳(H₀C)` equals
`Ind_{HC}^{HU}(hcPsi θbar)` for some nontrivial seed `θbar : H̄ →* ℂˣ`.

A constituent `ψ` of `Res_{HC} χ` kills `ker hcHom = H₀C` (kernel inheritance from
`H₀C ⊆ Ker χ`), so it factors through `hcHom : HC ↠ H̄` as `ψ = hcPsi θbar` (`H̄` abelian, the
factored character is linear).  If `θbar = 1` then `ψ` is the trivial (hence `HU`-invariant)
character and Clifford's invariant case (`restrict_eq_restrictionMultiplicity_smul_of_invariant`)
makes `Res_{HC} χ` constant, forcing `H ⊆ Ker χ` — contradicting `χ ∈ 𝒳`.  For `θbar ≠ 1` the
induction `Ind_{HC}(hcPsi θbar)` is irreducible (case-(b) inertia `inertia_eq_hcInHu`), so the
Clifford correspondence (`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`) gives
`χ = Ind_{HC}(hcPsi θbar)`. -/
theorem caseB_xiOf_H0C_eq_induce_hcPsi [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiOf data (chief.H0 ⊔ cSub data chief)) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ, θbar ≠ 1 ∧
      (χ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
  classical
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype (IrreducibleCharacter ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data))) := Fintype.ofFinite _
  obtain ⟨hχX, hχK⟩ := hχ
  obtain ⟨ψ, hψover⟩ := OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) χ
  have hN := realizedH0supCprime_normal_huSub chief
  have hNC := realizedH0supC_normal_huSub chief
  have hNsub : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hNC.subgroupOf _
  -- `ψ` kills `ker hcHom ⊆ H₀C ⊆ Ker χ`-inherited
  have hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    intro x hx
    have hx1 : hcHom chief x = 1 := hx
    have hxH0C : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) := by
      rw [hcHom, MonoidHom.comp_apply] at hx1
      have h2 : (QuotientGroup.mk' ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) x)
          = 1 := by
        apply (hcQuotientEquivHbar chief).injective
        rw [map_one]
        exact hx1
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff x).mp h2
    exact liesOver_mem_characterKernel hψover (hχK (Subgroup.mem_subgroupOf.mp hxH0C))
  -- factor `ψ` through `hcHom` and make the factor linear
  obtain ⟨ψbar, hψbar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) ψ hker
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbar⟩ :=
    ψbar.isIrreducible.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  have hψeq : (ψ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = (hcPsi chief θbar : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
    rw [← hψbar, ← hθbar]
    ext x
    simp [hcPsi, ClassFunction.compHom_apply,
      MonoidHom.comp_apply]
  have hψeq' : ψ = hcPsi chief θbar := IrreducibleCharacter.ext hψeq
  rcases eq_or_ne θbar 1 with rfl | hθne
  · -- trivial seed: `ψ` invariant, Clifford forces `H ⊆ Ker χ`, contradiction with `χ ∈ 𝒳`
    exfalso
    have hψtriv : (ψ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        = trivialClassFunction _ := by
      rw [hψeq]
      ext x
      simp [hcPsi, trivialClassFunction]
    have hinv : ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g ψ = ψ := by
      intro g
      apply IrreducibleCharacter.ext
      rw [IrreducibleCharacter.coe_conjBy, hψtriv]
      ext x
      simp [ClassFunction.conjBy_apply, trivialClassFunction]
    have hres := OddOrder.RepresentationTheory.restrict_eq_restrictionMultiplicity_smul_of_invariant
      (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      χ ψ hψover hinv
    apply hχX
    intro x hx
    rw [SetLike.mem_coe] at hx
    have hxHC : x ∈ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data) := Subgroup.mem_sup_left hx
    have h1 := congrArg (fun f : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ =>
      f (⟨x, hxHC⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))) hres
    have h2 := congrArg (fun f : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ =>
      f (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))) hres
    simp only [ClassFunction.restrict_apply, ClassFunction.smul_apply, hψtriv] at h1 h2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have htriv1 : (trivialClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        ClassFunction _ ℂ) (⟨x, hxHC⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
          M).subgroupOf (huSub data))) = 1 := rfl
    have htriv2 : (trivialClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        ClassFunction _ ℂ) (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
          M).subgroupOf (huSub data))) = 1 := rfl
    rw [htriv1] at h1
    rw [htriv2] at h2
    exact h1.trans h2.symm
  · -- nontrivial seed: Clifford correspondence
    have hθbarnt : (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        ≠ trivialClassFunction _ := by
      intro h0
      apply hθne
      rw [← linearIrreducibleCharacter_eq_trivial_iff]
      exact IrreducibleCharacter.ext
        (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
    have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
    refine ⟨θbar, hθne, ?_⟩
    exact OddOrder.RepresentationTheory.coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
      (G := ↥(huSub data)) χ (hcPsi chief θbar)
      (hcZeta_irreducible chief θbar hθ₀) (hψeq' ▸ hψover)

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Stages-flattening**: a `𝒮`-member whose (irreducible) source equals
`Ind_{HC}^{HU}(hcPsi θbar)` is induced from a linear character of the `M`-level `HC`
(`HC.map subtype`).  The case-split-free tail of the `isIndHC` lemmas: induction in stages
(`induce_induce_subgroupOf`) plus the `subgroupCongr` transport
(`induce_compHom_subgroupCongr`). -/
theorem isIndHC_of_source_eq_induce_hcPsi [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {ζ' : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hζ'eq : (ζ' : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          (hcPsi chief θbar).toClassFunction) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsi chief θbar : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsi chief θbar).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsi]
  · have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsi chief θbar : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsi chief θbar : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr!
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsi chief θbar : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Peterfalvi (13.3.a) core (Coq `PFsection9.isIndHC`)**: in Clifford case (b), every
*reducible* member of `𝒮(H₀)` is induced from a linear character of `HC` at the `M`-level.
Chain: (9.9.b) membership (`reducible_mem_sOf_H0C`), the `hcPsi`-exhaustion of `𝒳(H₀C)`
(`caseB_xiOf_H0C_eq_induce_hcPsi`), and induction in stages
`Ind^M_{HU} ∘ Ind^{HU}_{HC} = Ind^M_{HC}` (`induce_induce_subgroupOf`, with the
`subgroupCongr`-transport `induce_compHom_subgroupCongr` bridging the two spellings of the
`M`-level `HC`).  In the §13 instantiation `HC = PC`, so this is exactly the (13.3.a)
"`μ_j` is induced from a linear character of `PC`" shape. -/
theorem caseB_reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    [Fintype ↥M]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data chief.H0) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      φ = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype) := Fintype.ofFinite _
  let : Fintype ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  -- (9.9.b) membership + exhaustion
  have hφC := reducible_mem_sOf_H0C hG chars φ hφ hred
  obtain ⟨ζ', hζ'xi, rfl⟩ := mem_sOf.mp hφC
  obtain ⟨θbar, hθne, hζ'eq⟩ := caseB_xiOf_H0C_eq_induce_hcPsi caseB hζ'xi
  -- the `M`-level `HC` and the value-preserving iso back to the realized `HC`
  have hKle : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype ≤ huSub data :=
    Subgroup.map_subtype_le _
  have hKeq : ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype).subgroupOf (huSub data)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.comap_map_eq_self_of_injective (huSub data).subtype_injective _
  set f : ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).map (huSub data).subtype) ≃*
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    (Subgroup.subgroupOfEquivOfLe hKle).symm.trans (MulEquiv.subgroupCongr hKeq) with hf
  refine ⟨ClassFunction.compHom f.toMonoidHom
    (hcPsi chief θbar : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ),
    ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      f.surjective (hcPsi chief θbar).isIrreducible
  · rw [ClassFunction.compHom_apply, map_one]
    simp [hcPsi]
  · -- `Ind_{HU}^M (Ind_{HC}^{HU} ψ₀) = Ind_K^M (ψ₀ ∘ f)` by stages + `subgroupCongr` transport
    have hstages := OddOrder.RepresentationTheory.induce_induce_subgroupOf
      (M := ↥M) (K := (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)).map (huSub data).subtype) (H := huSub data) hKle
      (ClassFunction.compHom f.toMonoidHom
        (hcPsi chief θbar : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ))
    -- identify the inner induction with `Ind_{HC}^{HU}(hcPsi θbar)`
    have hfe : f.toMonoidHom.comp (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        = (MulEquiv.subgroupCongr hKeq).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [hf]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    have hcomp : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
        (ClassFunction.compHom f.toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ))
        = ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom
          (hcPsi chief θbar : ClassFunction
            ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data)) ℂ) := by
      rw [OddOrder.RepresentationTheory.ClassFunction.compHom_comp, hfe]
    have hinner : ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data
        chief).subgroupOf M).subgroupOf (huSub data)).map
          (huSub data).subtype).subgroupOf (huSub data))
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
          (ClassFunction.compHom f.toMonoidHom
            (hcPsi chief θbar : ClassFunction
              ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                (huSub data)) ℂ)))
        = ClassFunction.induce
            (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
            (hcPsi chief θbar).toClassFunction := by
      rw [hcomp]
      exact OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq _
    change induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = _
    calc induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ζ' : ClassFunction ↥(huSub data) ℂ) := by
          unfold induceHU
          congr!
      _ = ClassFunction.induce (huSub data)
            (ClassFunction.induce (((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
              M).subgroupOf (huSub data)).map (huSub data).subtype).subgroupOf (huSub data))
              (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
                (ClassFunction.compHom f.toMonoidHom
                  (hcPsi chief θbar : ClassFunction
                    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
                      (huSub data)) ℂ)))) := by rw [hinner, ← hζ'eq]
      _ = _ := hstages

end OddOrder.Peterfalvi.S11


