-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
-- name    : QEC_Coding_QuantumTanner_ArithmeticGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:31:55.47582+00:00
-- url     : https://prove2.me/theorems/c31ec6ba-dae7-43f8-8a4c-38c851ce13a9
-- title:
--   Arithmetic Geometry
-- statement:
--   Definitions and structural lemmas for Arithmetic Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ArithmeticGeometry.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantLeftSet_inv_mem
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantRightSet_inv_mem
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantSets_total_nonconjugacy
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedLeft_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_inverse
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexed_total_nonconjugacy
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]
instance finiteProjectiveGroup (epsilon y : K) : Fintype (ProjectiveGroup epsilon y) := by
  classical
  letI : Finite (Model epsilon y) := Finite.of_equiv (K × K × K × K)
    (QuaternionAlgebra.equivProd epsilon 0 (1 + y)).symm
  exact Fintype.ofFinite _
abbrev LeftIndex (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) := constantLeftSet f epsilon y hY hOne
abbrev RightIndex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :=
  constantRightSet f epsilon y hEpsilon hY hOne
instance finiteLeftIndex (f : F →+* K) (epsilon : F) (y : K)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Fintype (LeftIndex f epsilon y hY hOne) := by
  classical
  exact Fintype.ofFinite _
instance finiteRightIndex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Fintype (RightIndex f epsilon y hEpsilon hY hOne) := by
  classical
  exact Fintype.ofFinite _
def inversePerm {H : Type*} [Group H] (S : Set H)
    (hInverse : ∀ g ∈ S, g⁻¹ ∈ S) : Equiv.Perm S where
  toFun g := ⟨g.val⁻¹, hInverse g.val g.property⟩
  invFun g := ⟨g.val⁻¹, hInverse g.val g.property⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv g := by apply Subtype.ext; simp
def leftInverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Equiv.Perm (LeftIndex f epsilon y hY hOne) :=
  inversePerm _ (fun _ hg => constantLeftSet_inv_mem f epsilon y hEpsilon hY hOne hg)
def rightInverse (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    Equiv.Perm (RightIndex f epsilon y hEpsilon hY hOne) :=
  inversePerm _ (fun _ hg => constantRightSet_inv_mem f epsilon y hEpsilon hY hOne hg)
def squareComplex (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    LeftRightCayleySquareComplex (ProjectiveGroup (f epsilon) y)
      (LeftIndex f epsilon y hY hOne) (RightIndex f epsilon y hEpsilon hY hOne)
      (CayleySquare
        (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
        (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)) :=
  cayleySquareComplex
    (Subtype.val : LeftIndex f epsilon y hY hOne → ProjectiveGroup (f epsilon) y)
    (Subtype.val : RightIndex f epsilon y hEpsilon hY hOne → ProjectiveGroup (f epsilon) y)
    (leftInverse f epsilon y hEpsilon hY hOne)
    (rightInverse f epsilon y hEpsilon hY hOne)
    Subtype.val_injective Subtype.val_injective (fun _ => rfl) (fun _ => rfl)
    (fun g a b => constantSets_total_nonconjugacy f epsilon y hEpsilon hY hOne hTwo
      a.property b.property g)
def indexedSquareComplex [Fintype F] (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    LeftRightCayleySquareComplex (ProjectiveGroup (f epsilon) y)
      (TorusIndex epsilon) (TorusIndex epsilon)
      (CayleySquare (indexedLeft f epsilon y hTwoF hY hOne hTwo)
        (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)) :=
  cayleySquareComplex
    (indexedLeft f epsilon y hTwoF hY hOne hTwo)
    (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (indexedLeft_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedLeft_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (indexedRight_inverse f epsilon y hEpsilon hTwoF hY hOne hTwo)
    (fun g a b => indexed_total_nonconjugacy f epsilon y hEpsilon hTwoF hY hOne hTwo a b g)
end QEC.Coding.QuantumTanner.ArithmeticGeometry


