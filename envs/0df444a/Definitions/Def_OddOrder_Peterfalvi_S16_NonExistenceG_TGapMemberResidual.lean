-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapMemberResidual
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_TGapMemberResidual
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:04:12.080348+00:00
-- url     : https://prove2.me/theorems/73d31b58-f4db-4ef5-9d6b-ca5e6b897493
-- title:
--   Peterfalvi §11.8: member residual non-orthogonality
-- statement:
--   Provides producer-level bridges for applying the Section 11 non-orthogonality calculation to each member of the $T$-side coherent family.
--
--   Main declarations: `s12HypothesisOfTypePData` (Peterfalvi (10.1), the Section 12 carrier with a specified type-`P` decomposition).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapMemberResidual.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapMemberResidual.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IVBasic
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
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
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Peterfalvi (10.1), the Section 12 carrier with a specified type-`P`
decomposition.**  The standard existence theorem chooses an unspecified
`TypePData`.  For cross-construction comparisons we must retain the already
reconciled `W₁,W₂` factors; the faithful type-`P₁` Dade producer works for that
specified datum verbatim. -/
noncomputable def s12HypothesisOfTypePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.Peterfalvi.S12.Hypothesis M := by
  let dadeData :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
      hG hM data hP1).some
  exact
    { maximal := hM
      typeP := data
      type_alt := htype
      dadeData := dadeData }

end OddOrder.Peterfalvi.S16


