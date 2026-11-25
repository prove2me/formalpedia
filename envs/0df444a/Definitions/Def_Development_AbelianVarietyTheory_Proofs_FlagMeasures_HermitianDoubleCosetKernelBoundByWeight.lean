-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetKernelBoundByWeight
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetKernelBoundByWeight
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:03.493915+00:00
-- url     : https://prove2.me/theorems/f655724c-1d13-41f8-a7c0-d92bf1dd4c22
-- title:
--   Hermitian Double Coset Kernel Bound By Weight
-- statement:
--   Definitions and structural lemmas for Hermitian Double Coset Kernel Bound By Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetKernelBoundByWeight.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimatesStatement
import Theorems.Thm_GlobalTheory_HL_DualInter_smul_l
import Theorems.Thm_GlobalTheory_HL_DualInter_sub_l
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_add_left
import Theorems.Thm_GlobalTheory_HL_GaussSummand_hf_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.KernelWeight
section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_add_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (a + b) y =
      _root_.GlobalTheory.HL.hf L Hm a y + _root_.GlobalTheory.HL.hf L Hm b y := by
  have h := _root_.GlobalTheory.HL.DualInter.sub_l L Hm (a + b) b y
  rw [add_sub_cancel_right] at h
  linear_combination -h
open scoped Pointwise ENNReal Classical in
open ValuativeRel MeasureTheory in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
theorem _root_.GlobalTheory.HL.KernelWeight.hf_smul_left (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L Hm (c • a) y = c * _root_.GlobalTheory.HL.hf L Hm a y :=
  _root_.GlobalTheory.HL.DualInter.smul_l L Hm c a y
def hfLin (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := hf_add_left L Hm a b y
  map_smul' c a := hf_smul_left L Hm c a y
end
end GlobalTheory.HL.KernelWeight


