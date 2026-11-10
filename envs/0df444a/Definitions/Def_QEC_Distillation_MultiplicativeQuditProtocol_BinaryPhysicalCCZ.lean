-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:40:41.977703+00:00
-- url     : https://prove2.me/theorems/aeb3b09e-a184-4dbd-ab46-8d825f44a281
-- title:
--   Binary Physical CCZ
-- statement:
--   Definitions and structural lemmas for Binary Physical CCZ, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryPhysicalCCZ.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTripleSupport_disjoint
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
attribute [local simp] QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
def binaryTripleExponent (x : J × Fin 512)
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : ZMod 2 :=
  label (binaryTripleVertex J x .first) * label (binaryTripleVertex J x .second) *
    label (binaryTripleVertex J x .third)
def binaryTripleAmplitude (x : J × Fin 512)
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : Complex :=
  PauliSymplectic.binaryPhaseScalar (binaryTripleExponent x label)
theorem binarySign_square (p : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar p * PauliSymplectic.binaryPhaseScalar p = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hp : p + p = 0 := by fin_cases p <;> decide
  rw [hp, PauliSymplectic.binaryPhaseScalar_zero]
def binaryTripleCCZ (x : J × Fin 512) :
    UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) where
  toLinearEquiv := KT19PrimeQuditCSS.diagonalLinearEquiv
    (binaryTripleAmplitude x) (binaryTripleAmplitude x)
    (fun _ => binarySign_square _) (fun _ => binarySign_square _)
  map_inner := KT19PrimeQuditCSS.diagonalOperator_map_inner _ (fun label => by
    change PauliSymplectic.binaryPhaseScalar _ *
      star (PauliSymplectic.binaryPhaseScalar _) = 1
    rw [PauliSymplectic.binaryPhaseScalar_star]
    exact binarySign_square _)
@[simp] theorem binaryTripleCCZ_apply (x : J × Fin 512)
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryTripleCCZ x psi label = binaryTripleAmplitude x label * psi label := rfl
def binarySelectedSiteEquivFin (J : Type) [Fintype J] :
    Fin (Fintype.card {x // x ∈ binarySelectedSites J}) ≃ {x // x ∈ binarySelectedSites J} :=
  taggedCczSiteEquivFin _
def binaryPhysicalCCZ :
    UnitaryTransport (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) :=
  UnitaryTransport.composeFamily fun j =>
    binaryTripleCCZ (binarySelectedSiteEquivFin J j).val
def binarySelectedExponent
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) : ZMod 2 :=
  ∑ x ∈ binarySelectedSites J, binaryTripleExponent x label
inductive BinaryTripleLocalGate : Finset (TaggedThreeCopyCoordinate (J × Fin 512)) → Type
  | at (x : J × Fin 512) : BinaryTripleLocalGate (binaryTripleSupport J x)
def binaryPhysicalGateModel :
    FinitePhysicalGateModel (TaggedThreeCopyCoordinate (J × Fin 512))
      (TaggedThreeCopyRegister (ZMod 2) (J × Fin 512)) where
  LocalGate := BinaryTripleLocalGate
  realize gate := match gate with
    | .at x => binaryTripleCCZ x
def binaryPhysicalFactorization : PhysicalGateFactorization
    (binaryPhysicalGateModel (J := J)) binaryPhysicalCCZ where
  factorCount := Fintype.card {x // x ∈ binarySelectedSites J}
  support j := binaryTripleSupport J (binarySelectedSiteEquivFin J j).val
  factor j := .at (binarySelectedSiteEquivFin J j).val
  pairwise_disjoint := by
    intro a b hab
    apply binaryTripleSupport_disjoint
    intro heq
    exact hab ((binarySelectedSiteEquivFin J).injective (Subtype.ext heq))
  realizes := rfl
end QEC.Distillation.Ngu24Binary


