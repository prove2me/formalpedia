-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:15:18.541066+00:00
-- url     : https://prove2.me/theorems/c0988ec7-f34f-4478-82c2-2075e945baa4
-- title:
--   Peterfalvi §14: the subgroup $L$ and the $T$/$S$ case (b) data
-- statement:
--   Formalizes the post-(14.9) construction of $L$, the $T$- and $S$-side case (b) packages, and their structural consequences.
--
--   Main declarations: `CaseBForTData` (Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi (14.4)); `CaseBForSData` (Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi (14.6)); `fieldNormalizerKernelTransport` ((14.7) σ-bridge, kernel half); `fieldNormalizerComplementTransport` ((14.7) σ-bridge, complement half).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceGalois
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Carrier for the case-(9.7.b) conclusion applied to `T` in Peterfalvi
(14.4). -/
structure CaseBForTData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  D_eq_bot : hyp.base.D = ⊥
  v_eq : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)

/-- Carrier for the case-(9.7.b) conclusion applied to `S` in Peterfalvi
(14.6). -/
structure CaseBForSData (hyp : Hypothesis (G := G)) where
  caseB_formula : Prop
  caseB_holds : caseB_formula
  order_u_eq_of_p_modEq_one :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1))
  order_u_eq_of_not_modEq_one :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)
  U_rank_obstruction : Prop
  U_rank_obstruction_holds : U_rank_obstruction

/-- **(14.7) σ-bridge, kernel half.**  Given the Peterfalvi (14.2)(a) additive
isomorphism `e : Additive ↥P ≃+ 𝔽_{p^q}`, this is the transport homomorphism
`P = 𝔽_{p^q} →* G` sending a field point `s` to the group element `e⁻¹ s ∈ P ≤ G`.
It is the kernel (`inl`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerKernelTransport (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q) :
    fieldNormalizerAdditiveGroup hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  { toFun := fun m =>
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G)
    map_one' := by simp
    map_mul' := fun m n => by
      simp [toAdd_mul, map_add, toMul_add] }

@[simp] theorem fieldNormalizerKernelTransport_apply (hyp : Hypothesis (G := G))
    (e : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
    (m : fieldNormalizerAdditiveGroup hyp) :
    fieldNormalizerKernelTransport hyp e m =
      ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥hyp.base.P) : G) :=
  rfl

/-- **(14.7) σ-bridge, complement half.**  Given the Peterfalvi (14.2)(a)
multiplicative character `μ : U →* 𝔽_{p^q}ˣ` realizing `U` as the norm-one units `U*`,
this is the transport homomorphism `U* →* G` inverting `μ` and including back into `G`.
It is the complement (`inr`) factor of the field-normalizer embedding `σ`. -/
noncomputable def fieldNormalizerComplementTransport (hyp : Hypothesis (G := G))
    (μ : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ)
    (hμ_inj : Function.Injective μ)
    (hμ_range : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
         μ.range = OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :
    fieldNormalizerNormOneUnits hyp →* G :=
  letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
  let μ' : ↥hyp.base.U →* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    { toFun := fun u => ⟨μ u, hμ_range ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let eU : ↥hyp.base.U ≃* ↥(OddOrder.BG.AppC.NormSet.normOneUnits hyp.base.p hyp.base.q) :=
    MulEquiv.ofBijective μ'
      ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
       fun u => by
         obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
         exact ⟨v, Subtype.ext hv⟩⟩
  hyp.base.U.subtype.comp eU.symm.toMonoidHom

/-- `U` normalizes `P`: since `P = F(S)` is normal in `S` and `U ≤ S' = PU ≤ S`. -/
theorem U_le_normalizer_P (hyp : Hypothesis (G := G)) :
    hyp.base.U ≤ Subgroup.normalizer hyp.base.P := by
  have hU_le_deriv : hyp.base.U ≤ derivedInG hyp.base.S := by
    rw [hyp.base.S_deriv_eq_PU]; exact le_sup_right
  have hderiv_le_S : derivedInG hyp.base.S ≤ hyp.base.S := Subgroup.map_subtype_le _
  have hS_le_norm : hyp.base.S ≤ Subgroup.normalizer hyp.base.P := by
    rw [hyp.base.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.S
  exact (hU_le_deriv.trans hderiv_le_S).trans hS_le_norm

/-- **(14.7) `hUP` input**: conjugating a point of `P` by an element of `U` stays in `P`. -/
theorem conj_mem_P (hyp : Hypothesis (G := G)) (v : ↥hyp.base.U) (x : ↥hyp.base.P) :
    (v : G) * (x : G) * (v : G)⁻¹ ∈ hyp.base.P := by
  have hv : (v : G) ∈ Subgroup.normalizer hyp.base.P := U_le_normalizer_P hyp v.2
  exact (Subgroup.mem_normalizer_iff.mp hv (x : G)).mp x.2

end OddOrder.Peterfalvi.S16


