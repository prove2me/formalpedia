-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
-- name    : QEC_Coding_ExpanderCodes_TannerLiftedProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:11:19.145934+00:00
-- url     : https://prove2.me/theorems/0bbd5a34-2821-40fe-86c8-0dc7e60f222a
-- title:
--   Tanner Lifted Product
-- statement:
--   Definitions and structural lemmas for Tanner Lifted Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
def doubleCoverVoltage (label : W → G) (side : Fin 2) (j : W) : G :=
  if side = 0 then 1 else label j
noncomputable def doubleCoverTannerMatrix
    (label : W → G) (h : Matrix R W F) :
    Matrix (Fin 2 × R) W (MonoidAlgebra F G) :=
  fun ir j =>
    MonoidAlgebra.single (doubleCoverVoltage label ir.1 j) (h ir.2 j)
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] in
@[simp]
theorem doubleCoverTannerMatrix_zeroSide_apply
    (label : W → G) (h : Matrix R W F) (r : R) (j : W) :
    doubleCoverTannerMatrix label h (0, r) j =
      MonoidAlgebra.single 1 (h r j) := by
  simp [doubleCoverTannerMatrix, doubleCoverVoltage]
omit [Fintype F] [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] in
@[simp]
theorem doubleCoverTannerMatrix_oneSide_apply
    (label : W → G) (h : Matrix R W F) (r : R) (j : W) :
    doubleCoverTannerMatrix label h (1, r) j =
      MonoidAlgebra.single (label j) (h r j) := by
  simp [doubleCoverTannerMatrix, doubleCoverVoltage]
noncomputable def data (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    LiftedProduct.Data F G (Fin 2 × R) W W (Fin 2 × R') where
  A := doubleCoverTannerMatrix label h
  B := LiftedProduct.starTranspose (doubleCoverTannerMatrix label g')
noncomputable def boundary1SupportCover
    (label : W → G) (_h : Matrix R W F) (_g' : Matrix R' W F)
    (c0 : LiftedProduct.C0Index (Fin 2 × R) W G) :
    Finset (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) := by
  classical
  rcases c0 with ⟨ar, br, go⟩
  let leftEmbedding : W ↪
      LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
    ⟨fun ac => Sum.inl
      (ac, br, go * (doubleCoverVoltage label ar.1 ac)⁻¹), by
        intro x y hxy
        simpa using congrArg (fun z => z.1) (Sum.inl.inj hxy)⟩
  let rightEmbedding : (Fin 2 × R') ↪
      LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
    ⟨fun bc => Sum.inr
      (ar, bc, doubleCoverVoltage label bc.1 br * go), by
        intro x y hxy
        simpa using congrArg (fun z => z.2.1) (Sum.inr.inj hxy)⟩
  exact Finset.univ.map leftEmbedding ∪ Finset.univ.map rightEmbedding
noncomputable def boundary2SupportCover
    (label : W → G) (_h : Matrix R W F) (_g' : Matrix R' W F)
    (c2 : LiftedProduct.C2Index W (Fin 2 × R') G) :
    Finset (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) := by
  classical
  rcases c2 with ⟨ac, bc, gi⟩
  let leftEmbedding : W ↪
      LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
    ⟨fun br => Sum.inl
      (ac, br, (doubleCoverVoltage label bc.1 br)⁻¹ * gi), by
        intro x y hxy
        simpa using congrArg (fun z => z.2.1) (Sum.inl.inj hxy)⟩
  let rightEmbedding : (Fin 2 × R) ↪
      LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G :=
    ⟨fun ar => Sum.inr
      (ar, bc, gi * doubleCoverVoltage label ar.1 ac), by
        intro x y hxy
        simpa using congrArg (fun z => z.1) (Sum.inr.inj hxy)⟩
  exact Finset.univ.map leftEmbedding ∪ Finset.univ.map rightEmbedding
noncomputable def variableSupportCover
    (label : W → G) (_h : Matrix R W F) (_g' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :
    Finset (Sum
      (LiftedProduct.C0Index (Fin 2 × R) W G)
      (LiftedProduct.C2Index W (Fin 2 × R') G)) := by
  classical
  cases q with
  | inl q =>
      rcases q with ⟨ac, br, gi⟩
      let lowerEmbedding : (Fin 2 × R) ↪ Sum
          (LiftedProduct.C0Index (Fin 2 × R) W G)
          (LiftedProduct.C2Index W (Fin 2 × R') G) :=
        ⟨fun ar => Sum.inl
          (ar, br, gi * doubleCoverVoltage label ar.1 ac), by
            intro x y hxy
            simpa using congrArg (fun z => z.1) (Sum.inl.inj hxy)⟩
      let upperEmbedding : (Fin 2 × R') ↪ Sum
          (LiftedProduct.C0Index (Fin 2 × R) W G)
          (LiftedProduct.C2Index W (Fin 2 × R') G) :=
        ⟨fun bc => Sum.inr
          (ac, bc, doubleCoverVoltage label bc.1 br * gi), by
            intro x y hxy
            simpa using congrArg (fun z => z.2.1) (Sum.inr.inj hxy)⟩
      exact Finset.univ.map lowerEmbedding ∪ Finset.univ.map upperEmbedding
  | inr q =>
      rcases q with ⟨ar, bc, gi⟩
      let lowerEmbedding : W ↪ Sum
          (LiftedProduct.C0Index (Fin 2 × R) W G)
          (LiftedProduct.C2Index W (Fin 2 × R') G) :=
        ⟨fun br => Sum.inl
          (ar, br, (doubleCoverVoltage label bc.1 br)⁻¹ * gi), by
            intro x y hxy
            simpa using congrArg (fun z => z.2.1) (Sum.inl.inj hxy)⟩
      let upperEmbedding : W ↪ Sum
          (LiftedProduct.C0Index (Fin 2 × R) W G)
          (LiftedProduct.C2Index W (Fin 2 × R') G) :=
        ⟨fun ac => Sum.inr
          (ac, bc, gi * (doubleCoverVoltage label ar.1 ac)⁻¹), by
            intro x y hxy
            simpa using congrArg (fun z => z.1) (Sum.inr.inj hxy)⟩
      exact Finset.univ.map lowerEmbedding ∪ Finset.univ.map upperEmbedding
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
universe w
variable {F G W R R' : Type w}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
noncomputable local instance _p2m_local_instance_68799ef5cb_575 : DecidableEq
    (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :=
  Classical.decEq _
noncomputable def semanticPresentation
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :=
  QEC.Coding.FiniteFieldCSSPresentation.presentation
    (LiftedProduct.chainComplex (data label h g'))
end QEC.Coding.TannerLiftedProduct


