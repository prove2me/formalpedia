-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
-- name    : QEC_Coding_QuantumTanner_LiftedProductTannerBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T01:07:10.091503+00:00
-- url     : https://prove2.me/theorems/881f910f-1c1e-4734-839f-1f5c20cb8e57
-- title:
--   Lifted Product Tanner Bridge
-- statement:
--   Definitions and structural lemmas for Lifted Product Tanner Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTensorBridge_tensorMatrix_mem
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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
namespace QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
def selectedZWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gB : Matrix D' B (ZMod 2)) (a : A → G) (b : B → G)
    (U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
      Matrix C D' (MonoidAlgebra (ZMod 2) G)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => zWord hA hB a b
    (zParameter (U.1 * twistedMatrix gB (fun j => (b j)⁻¹)) (U.2 * scalarMatrix gB))
    (retainedCoordinate i j g)
def selectedXWord (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (a : A → G) (b : B → G)
    (V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
      Matrix C' D (MonoidAlgebra (ZMod 2) G)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => xWord hA hB a b
    (xParameter ((scalarMatrix gA).transpose * V.1)
      ((twistedMatrix gA (fun i => (a i)⁻¹)).transpose * V.2))
    (retainedCoordinate i j g)
def parameterSections (P : Matrix C A (ZMod 2)) (Q : Matrix D B (ZMod 2))
    (U : Matrix C D (MonoidAlgebra (ZMod 2) G)) :
    G → (tensorCode (matrixRowCode P) (matrixRowCode Q)).carrier :=
  fun u => ⟨tensorMatrix P Q (fun c d => (U c d).coeff u), tensorMatrix_mem P Q _⟩
def tannerZMap (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    ((G → L.carrier) × (G → L.carrier)) →ₗ[ZMod 2] Word (ZMod 2) (A × B × G) where
  toFun T := fun (i, j, g) => (T.1 (g * b j)).val (i, j) + (T.2 (a i * g)).val (i, j)
  map_add' T S := by ext ⟨i, j, g⟩; simp [add_assoc, add_left_comm, add_comm]
  map_smul' k T := by ext ⟨i, j, g⟩; simp [mul_add]
def tannerXMap (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    ((G → L.carrier) × (G → L.carrier)) →ₗ[ZMod 2] Word (ZMod 2) (A × B × G) where
  toFun T := fun (i, j, g) => (T.1 g).val (i, j) + (T.2 (a i * g * b j)).val (i, j)
  map_add' T S := by ext ⟨i, j, g⟩; simp [add_assoc, add_left_comm, add_comm]
  map_smul' k T := by ext ⟨i, j, g⟩; simp [mul_add]
def chartVertex (a : A → G) (b : B → G) (left right : Bool)
    (i : A) (j : B) (g : G) : G :=
  (if left then a i * g else g) * (if right then b j else 1)
def chartExtension (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) : Word (ZMod 2) (A × B × G) :=
  fun (i, j, g) => if u = chartVertex a b left right i j g then x (i, j) else 0
def chartLink (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (ij : A × B) : A × B × G :=
  (ij.1, ij.2, (if left then (a ij.1)⁻¹ * u else u) *
    (if right then (b ij.2)⁻¹ else 1))
def tannerZChecks (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    Submodule (ZMod 2) (Word (ZMod 2) (A × B × G)) :=
  Submodule.span (ZMod 2)
    (Set.range (fun ux : G × L.carrier => chartExtension a b false true ux.1 ux.2.val) ∪
      Set.range (fun ux : G × L.carrier => chartExtension a b true false ux.1 ux.2.val))
def tannerXChecks (a : A → G) (b : B → G) (L : LinearCode (ZMod 2) (A × B)) :
    Submodule (ZMod 2) (Word (ZMod 2) (A × B × G)) :=
  Submodule.span (ZMod 2)
    (Set.range (fun ux : G × L.carrier => chartExtension a b false false ux.1 ux.2.val) ∪
      Set.range (fun ux : G × L.carrier => chartExtension a b true true ux.1 ux.2.val))
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge


