-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
-- name    : QEC_Distillation_LowOverheadProtocol_Core_Decoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:56:46.596202+00:00
-- url     : https://prove2.me/theorems/7c00618e-4a97-4896-bd3e-4601ef2b3158
-- title:
--   Decoder
-- statement:
--   Definitions and structural lemmas for Decoder, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Decoder.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18LogicalPlusInput_norm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
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
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
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
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
def ambientEncodingIsometry : LogicalRegister →ₗᵢ[Complex] PhysicalRegister :=
  HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier.subtypeₗᵢ.comp
    HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.toLinearIsometry
@[simp] theorem ambientEncodingIsometry_apply (psi : LogicalRegister) :
    ambientEncodingIsometry psi =
      (HH18NoisyInput.hh18_15_1_0_encodedCode.encoding psi : PhysicalRegister) :=
  rfl
def codeDecoderBranch : PhysicalRegister →ₗ[Complex] LogicalRegister :=
  LinearMap.adjoint ambientEncodingIsometry.toLinearMap
@[simp] theorem codeDecoderBranch_encoded (psi : LogicalRegister) :
    codeDecoderBranch (ambientEncodingIsometry psi) = psi := by
  change LinearMap.adjoint ambientEncodingIsometry.toLinearMap
    (ambientEncodingIsometry.toLinearMap psi) = psi
  exact LinearMap.congr_fun ambientEncodingIsometry.adjoint_comp_self' psi
theorem adjoint_codeDecoderBranch : LinearMap.adjoint codeDecoderBranch =
    ambientEncodingIsometry.toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]
def decoderCodeProjector : Operator PhysicalRegister :=
  (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch
@[simp] theorem decoderCodeProjector_encoded (psi : LogicalRegister) :
    decoderCodeProjector (ambientEncodingIsometry psi) = ambientEncodingIsometry psi := by
  change LinearMap.adjoint codeDecoderBranch
    (codeDecoderBranch (ambientEncodingIsometry psi)) = ambientEncodingIsometry psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl
theorem codeDecoderBranch_comp_adjoint :
    codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact ambientEncodingIsometry.adjoint_comp_self'
theorem decoderCodeProjector_idempotent :
    decoderCodeProjector.comp decoderCodeProjector = decoderCodeProjector := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch).comp
        ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch) =
      (LinearMap.adjoint codeDecoderBranch).comp
        ((codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch)).comp
          codeDecoderBranch) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint codeDecoderBranch).comp
          ((1 : Operator LogicalRegister).comp codeDecoderBranch) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch := by
      ext psi
      rfl
theorem decoderCodeProjector_adjoint :
    LinearMap.adjoint decoderCodeProjector = decoderCodeProjector := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]
def decoderComplementProjector : Operator PhysicalRegister := 1 - decoderCodeProjector
theorem decoderComplementProjector_adjoint :
    LinearMap.adjoint decoderComplementProjector = decoderComplementProjector := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]
theorem decoderComplementProjector_idempotent :
    decoderComplementProjector.comp decoderComplementProjector = decoderComplementProjector := by
  ext psi
  have hprojector := LinearMap.congr_fun decoderCodeProjector_idempotent psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp] theorem decoderComplementProjector_encoded (psi : LogicalRegister) :
    decoderComplementProjector (ambientEncodingIsometry psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf
noncomputable def decoderFallbackState : LogicalRegister :=
  EuclideanSpace.basisFun (Bitstring (HH18PuncturedReedMuller.LogicalSite 4 0)) Complex
    (fun _ => 0)
theorem decoderFallbackState_inner_self :
    inner Complex decoderFallbackState decoderFallbackState = 1 := by
  simp [decoderFallbackState]
theorem decoderFallbackState_normSq : ‖decoderFallbackState‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), decoderFallbackState_inner_self]
  norm_num
noncomputable def decoderPhysicalBasis :=
  stdOrthonormalBasis Complex PhysicalRegister
def complementDecoderBranch
    (i : Fin (Module.finrank Complex PhysicalRegister)) :
    PhysicalRegister →ₗ[Complex] LogicalRegister :=
  (InnerProductSpace.rankOne Complex decoderFallbackState
    (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap
theorem complementDecoderBranch_adjoint_comp
    (i : Fin (Module.finrank Complex PhysicalRegister)) :
    (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex decoderFallbackState
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        decoderFallbackState).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex decoderFallbackState
      (decoderComplementProjector (decoderPhysicalBasis i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq
  simp [LinearMap.comp_apply, hnormSq]
theorem sum_complementDecoderBranch_adjoint_comp :
    ∑ i : Fin (Module.finrank Complex PhysicalRegister),
      (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
        decoderComplementProjector := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector (decoderPhysicalBasis i))
      (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      decoderComplementProjector.comp (LinearMap.adjoint decoderComplementProjector) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← decoderPhysicalBasis.sum_repr'
          (LinearMap.adjoint decoderComplementProjector psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = decoderComplementProjector.comp decoderComplementProjector := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector := decoderComplementProjector_idempotent
def decoderKrausFamily :
    FiniteKrausFamily (Sum Unit (Fin (Module.finrank Complex PhysicalRegister)))
      PhysicalRegister LogicalRegister where
  operator
    | .inl _ => codeDecoderBranch
    | .inr i => complementDecoderBranch i
theorem decoderKrausFamily_complete : decoderKrausFamily.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector) +
      (∑ i : Fin (Module.finrank Complex PhysicalRegister),
        (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]
noncomputable def decoderChannel : QuantumChannel PhysicalRegister LogicalRegister :=
  decoderKrausFamily.toQuantumChannel decoderKrausFamily_complete
noncomputable def idealLogicalTOutputState : LogicalRegister :=
  HH18PuncturedReedMuller.logicalT 0 4 HH18NoisyInput.hh18LogicalPlusInput
theorem idealLogicalTOutputState_normSq : ‖idealLogicalTOutputState‖ ^ 2 = 1 := by
  have hnorm : ‖idealLogicalTOutputState‖ = 1 := by
    change ‖(HH18PuncturedReedMuller.logicalT 0 4).toLinearIsometryEquiv
      HH18NoisyInput.hh18LogicalPlusInput‖ = 1
    rw [(HH18PuncturedReedMuller.logicalT 0 4).toLinearIsometryEquiv.norm_map]
    exact hh18LogicalPlusInput_norm
  rw [hnorm]
  norm_num
noncomputable def idealLogicalTOutput : DensityOperator LogicalRegister :=
  DensityOperator.pureDensity idealLogicalTOutputState idealLogicalTOutputState_normSq
noncomputable def hh18OutputTraceError
    (rho sigma : DensityOperator LogicalRegister) : ℝ :=
  traceNorm (rho.toOperator - sigma.toOperator)
end HH18Protocol
end Distillation
end QEC


