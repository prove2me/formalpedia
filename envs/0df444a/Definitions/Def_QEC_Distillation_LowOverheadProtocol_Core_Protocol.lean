-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
-- name    : QEC_Distillation_LowOverheadProtocol_Core_Protocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:23:04.467439+00:00
-- url     : https://prove2.me/theorems/491e85d3-43b0-4ee6-b87a-a0fdc75b07f3
-- title:
--   Protocol
-- statement:
--   Definitions and structural lemmas for Protocol, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
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
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_measure
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependCoin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependDeterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependSyndrome
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_ledger_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_clifford
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_discard
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_zeroPreparation
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_operator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_conditionalDensity_toOperator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_ZeroPreparationAdapter_run_toOperator
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
import Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedOutputTraceError_le_two_mul_acceptedResidual
import Theorems.Thm_QEC_Distillation_HH18Protocol_acceptedResidualError_le_cubic
import Theorems.Thm_QEC_Distillation_HH18Protocol_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_eq_rawSuccessMass
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputRawError_le_cubic
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18NextInputRawError_le_outputTrace
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18OutputTraceError_nonneg
import Theorems.Thm_QEC_Distillation_HH18Protocol_noisyResources_permitted
import Theorems.Thm_QEC_Distillation_HH18Protocol_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos
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
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
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
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependCoin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependDeterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependSyndrome
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.ledger_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_discard
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_zeroPreparation
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_operator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
attribute [local simp] QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_adverse
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_favorable
attribute [local simp] QEC.Distillation.HH18Postselection.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Protocol.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Protocol.prepareMeasuredResources_toOperator
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
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
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
universe u
attribute [local instance 100] Fintype.ofFinite
local instance instProtocolClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
noncomputable def hh18MagicStateDistillationProtocol
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    MagicStateDistillationProtocol QubitSpace PhysicalRegister LogicalRegister where
  run := resourceDecodedRun (noisyResources epsilon)
  inputErrorModel := .independent (independentInputModel epsilon)
  inputPermitted := noisyResources_permitted epsilon
  behavior := .postselected
  idealOutput := idealLogicalTOutput
  outputError := hh18OutputTraceError
  outputError_nonneg := hh18OutputTraceError_nonneg
theorem hh18MagicStateDistillationProtocol_successfulOutputError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18MagicStateDistillationProtocol epsilon).successfulOutputError =
      hh18OutputTraceError
        (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
        idealLogicalTOutput :=
  rfl
def hh18NextInputSmallDomain (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  (2 * residualCubicCoefficient) * epsilon.1 ^ 3 ≤ 1 / 2
noncomputable def hh18NextInputErrorRate
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) : HH18NoisyInput.DiagonalErrorRate :=
  ⟨hh18NextInputRawError epsilon,
    hh18NextInputRawError_nonneg epsilon,
    (hh18NextInputRawError_le_cubic epsilon).trans hsmall⟩
theorem hh18NextInputErrorRate_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18NextInputSmallDomain epsilon) :
    (hh18NextInputErrorRate epsilon hsmall).1 ≤
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
  change hh18NextInputRawError epsilon ≤
    (2 * residualCubicCoefficient) * epsilon.1 ^ 3
  calc
    hh18NextInputRawError epsilon ≤
        hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput := hh18NextInputRawError_le_outputTrace epsilon
    _ ≤ 2 * acceptedResidualError epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
    _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) := by
      exact mul_le_mul_of_nonneg_left (acceptedResidualError_le_cubic epsilon) (by norm_num)
    _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by ring
noncomputable def hh18AcceptedRunOutputAsNextInput
    (run : DistillationRun QubitSpace PhysicalRegister LogicalRegister) :
    DensityOperator QubitSpace :=
  (phaseShiftTransport (-Real.pi / 2)).conjDensity
    (aBasisDephasing.mapDensity
      (hh18LogicalOutputTransport.conjDensity
        run.acceptedOutput))
noncomputable def hh18AcceptedOutputAsNextInput
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : DensityOperator QubitSpace :=
  hh18AcceptedRunOutputAsNextInput (resourceDecodedRun (noisyResources epsilon))
theorem expectedAcceptedPorts_eq_explicit_selected_mass
    {Port Outcome : Type u} [Fintype Port] [Fintype Outcome]
    (batch : DependentBatch.FiniteFlaggedBatch Port Outcome)
    (support : Finset Outcome) (selected : Outcome → Prop) [DecidablePred selected]
    (mass : ℝ)
    (hsupport : (Finset.univ : Finset Outcome) = support)
    (hcount : ∀ outcome, DependentBatch.acceptedPortCount batch outcome =
      if selected outcome then 1 else 0)
    (hmass : mass = support.sum fun outcome =>
      if selected outcome then batch.weight outcome else 0) :
    DependentBatch.expectedAcceptedPorts batch = mass := by
  unfold DependentBatch.expectedAcceptedPorts
  rw [hsupport]
  calc
    (∑ outcome ∈ support, batch.weight outcome *
        (DependentBatch.acceptedPortCount batch outcome : ℝ)) =
        support.sum (fun outcome =>
          if selected outcome then batch.weight outcome else 0) := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [hcount outcome]
      by_cases hselected : selected outcome <;> simp [hselected]
    _ = mass := hmass.symm
abbrev BatchInputSlot := Fin resourceCount
abbrev BatchOutputPort := Fin 1
noncomputable def hh18IterationScale : ℝ :=
  2 * residualCubicCoefficient + 30
theorem residualCubicCoefficient_nonneg :
    0 ≤ residualCubicCoefficient := by
  unfold residualCubicCoefficient
  positivity
theorem hh18IterationScale_pos : 0 < hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [residualCubicCoefficient_nonneg]
theorem hh18IterationScale_nonneg : 0 ≤ hh18IterationScale :=
  hh18IterationScale_pos.le
theorem hh18IterationScale_one_le : 1 ≤ hh18IterationScale := by
  unfold hh18IterationScale
  nlinarith [residualCubicCoefficient_nonneg]
theorem two_mul_residualCubicCoefficient_le_iterationScale_sq :
    2 * residualCubicCoefficient ≤ hh18IterationScale ^ 2 := by
  calc
    2 * residualCubicCoefficient ≤ hh18IterationScale := by
      unfold hh18IterationScale
      linarith
    _ = hh18IterationScale * 1 := by ring
    _ ≤ hh18IterationScale * hh18IterationScale :=
      mul_le_mul_of_nonneg_left hh18IterationScale_one_le hh18IterationScale_nonneg
    _ = hh18IterationScale ^ 2 := by ring
def hh18InitialSmallDomain (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  hh18IterationScale * epsilon.1 ≤ 1 / 2
structure HH18IterationState where
  rate : HH18NoisyInput.DiagonalErrorRate
  scaled_small : hh18IterationScale * rate.1 ≤ 1 / 2
theorem hh18IterationScale_sq_le_cube :
    hh18IterationScale ^ 2 ≤ hh18IterationScale ^ 3 := by
  calc
    hh18IterationScale ^ 2 = hh18IterationScale ^ 2 * 1 := by ring
    _ ≤ hh18IterationScale ^ 2 * hh18IterationScale :=
      mul_le_mul_of_nonneg_left hh18IterationScale_one_le
        (sq_nonneg hh18IterationScale)
    _ = hh18IterationScale ^ 3 := by ring
theorem scaled_cube_le_half (state : HH18IterationState) :
    hh18IterationScale ^ 2 * state.rate.1 ^ 3 ≤ 1 / 2 := by
  have hrate : 0 ≤ state.rate.1 := state.rate.property.1
  have hscaled_cube :
      (hh18IterationScale * state.rate.1) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_nonneg hrate) state.scaled_small 3
  calc
    hh18IterationScale ^ 2 * state.rate.1 ^ 3 ≤
        hh18IterationScale ^ 3 * state.rate.1 ^ 3 :=
      mul_le_mul_of_nonneg_right hh18IterationScale_sq_le_cube
        (pow_nonneg hrate 3)
    _ = (hh18IterationScale * state.rate.1) ^ 3 := by ring
    _ ≤ (1 / 2 : ℝ) ^ 3 := hscaled_cube
    _ ≤ 1 / 2 := by norm_num
theorem hh18IterationNextSmall (state : HH18IterationState) :
    hh18NextInputSmallDomain state.rate := by
  unfold hh18NextInputSmallDomain
  calc
    (2 * residualCubicCoefficient) * state.rate.1 ^ 3 ≤
        hh18IterationScale ^ 2 * state.rate.1 ^ 3 :=
      mul_le_mul_of_nonneg_right
        two_mul_residualCubicCoefficient_le_iterationScale_sq
        (pow_nonneg state.rate.property.1 3)
    _ ≤ 1 / 2 := scaled_cube_le_half state
theorem hh18IterationNextScaledSmall (state : HH18IterationState) :
    hh18IterationScale *
        (hh18NextInputErrorRate state.rate (hh18IterationNextSmall state)).1 ≤ 1 / 2 := by
  have hnext := hh18NextInputErrorRate_le_cubic state.rate
    (hh18IterationNextSmall state)
  have hscaled_cube :
      (hh18IterationScale * state.rate.1) ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀
      (mul_nonneg hh18IterationScale_nonneg state.rate.property.1)
      state.scaled_small 3
  calc
    hh18IterationScale *
        (hh18NextInputErrorRate state.rate (hh18IterationNextSmall state)).1 ≤
        hh18IterationScale *
          ((2 * residualCubicCoefficient) * state.rate.1 ^ 3) :=
      mul_le_mul_of_nonneg_left hnext hh18IterationScale_nonneg
    _ ≤ hh18IterationScale *
          (hh18IterationScale ^ 2 * state.rate.1 ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          two_mul_residualCubicCoefficient_le_iterationScale_sq
          (pow_nonneg state.rate.property.1 3))
        hh18IterationScale_nonneg
    _ = (hh18IterationScale * state.rate.1) ^ 3 := by ring
    _ ≤ (1 / 2 : ℝ) ^ 3 := hscaled_cube
    _ ≤ 1 / 2 := by norm_num
noncomputable def hh18IterationState
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) : Nat → HH18IterationState
  | 0 => ⟨epsilon, hsmall⟩
  | depth + 1 =>
      let previous := hh18IterationState epsilon hsmall depth
      ⟨hh18NextInputErrorRate previous.rate (hh18IterationNextSmall previous),
        hh18IterationNextScaledSmall previous⟩
noncomputable def hh18ErrorIteration
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    HH18NoisyInput.DiagonalErrorRate :=
  (hh18IterationState epsilon hsmall depth).rate
noncomputable def hh18ActualStageRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :=
  resourceDecodedRun (noisyResources (hh18ErrorIteration epsilon hsmall depth))
noncomputable def hh18CubicErrorEnvelope
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Nat → ℝ
  | 0 => epsilon.1
  | depth + 1 =>
      hh18IterationScale ^ 2 * (hh18CubicErrorEnvelope epsilon depth) ^ 3
abbrev hh18DepthInputSlots (depth : Nat) := Fin depth → BatchInputSlot
abbrev hh18DepthOutputSlots (depth : Nat) := Fin depth → BatchOutputPort
noncomputable def hh18DepthYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : NNReal := by
  classical
  exact ⟨∏ stage : Fin depth,
    rawSuccessMass (hh18ErrorIteration epsilon hsmall stage.1),
    Finset.prod_nonneg fun stage _ => (rawSuccessMass_pos _).le⟩
noncomputable def hh18DepthSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (hh18DepthInputSlots depth)
    (hh18DepthOutputSlots depth) (hh18DepthYieldFactor epsilon hsmall depth)
def hh18DepthSuccessorRouting (_depth : Nat) :
    Fin resourceCount × BatchOutputPort ≃ BatchOutputPort × Fin resourceCount :=
  DependentBatch.transposeRouting resourceCount 1
noncomputable def hh18DepthStageResource
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ResourceInput resourceCount QubitSpace :=
  noisyResources (hh18ErrorIteration epsilon hsmall depth)
def hh18DepthRoutedChildInputSlot (depth : Nat)
    (port : BatchOutputPort) (parent : Fin resourceCount) :
    BatchOutputPort × Fin resourceCount :=
  hh18DepthSuccessorRouting depth
    (DependentBatch.childInputSlot port parent)
@[simp] theorem hh18DepthRoutedChildInputSlot_apply (depth : Nat)
    (port : BatchOutputPort) (parent : Fin resourceCount) :
    hh18DepthRoutedChildInputSlot depth port parent = (port, parent) :=
  rfl
noncomputable def hh18DepthFreshParentRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (_parent : Fin resourceCount) :=
  hh18ActualStageRun epsilon hsmall depth
noncomputable def hh18DepthFreshParentAcceptedNextInput
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat)
    (source : BatchOutputPort × Fin resourceCount) : DensityOperator QubitSpace :=
  hh18AcceptedRunOutputAsNextInput
    (hh18DepthFreshParentRun epsilon hsmall depth source.2)
noncomputable def hh18DepthRoutedChildResources
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :
    ResourceInput resourceCount QubitSpace :=
  fun parent => hh18DepthFreshParentAcceptedNextInput epsilon hsmall depth
    (hh18DepthRoutedChildInputSlot depth 0 parent)
noncomputable def hh18DepthRoutedChildRun
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) :=
  resourceDecodedRun (hh18DepthRoutedChildResources epsilon hsmall depth)
noncomputable def oneLevelFlaggedBatch
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    DependentBatch.FiniteFlaggedBatch BatchOutputPort PhysicalErrorWord where
  weight := HH18NoisyInput.errorWordWeight epsilon
  weight_nonneg := HH18NoisyInput.errorWordWeight_nonneg epsilon
  total_weight := by
    simpa using HH18NoisyInput.errorWordWeight_sum (ι := PhysicalSite) epsilon
  accepted := fun error _ => decide (HH18SyndromeDecoding.Accepts error)
theorem oneLevelFlaggedBatch_acceptedPortCount
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord) :
    DependentBatch.acceptedPortCount (oneLevelFlaggedBatch epsilon) error =
      if HH18SyndromeDecoding.Accepts error then 1 else 0 := by
  classical
  unfold DependentBatch.acceptedPortCount
  by_cases haccept : HH18SyndromeDecoding.Accepts error <;>
    simp [oneLevelFlaggedBatch, haccept]
noncomputable def oneLevelExpectedYield
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  DependentBatch.expectedAcceptedPorts (oneLevelFlaggedBatch epsilon)
theorem oneLevelExpectedYield_eq_success
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    oneLevelExpectedYield epsilon = endpointWeight (noisyResources epsilon) .accepted := by
  calc
    oneLevelExpectedYield epsilon = rawSuccessMass epsilon := by
      unfold oneLevelExpectedYield
      exact expectedAcceptedPorts_eq_explicit_selected_mass
        (oneLevelFlaggedBatch epsilon) physicalErrorWords HH18SyndromeDecoding.Accepts
        (rawSuccessMass epsilon) (by rfl)
        (oneLevelFlaggedBatch_acceptedPortCount epsilon) (by rfl)
    _ = endpointWeight (noisyResources epsilon) .accepted :=
      (endpointWeight_accepted_eq_rawSuccessMass epsilon).symm
theorem oneLevelExpectedYield_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < oneLevelExpectedYield epsilon := by
  rw [oneLevelExpectedYield_eq_success]
  exact endpointWeight_accepted_pos epsilon
noncomputable def oneLevelYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : NNReal :=
  ⟨oneLevelExpectedYield epsilon, (oneLevelExpectedYield_pos epsilon).le⟩
noncomputable def oneLevelSuccessfulOutputCost
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost BatchInputSlot BatchOutputPort
    (oneLevelYieldFactor epsilon)
noncomputable def oneLevelInputOutputRatio : ℝ :=
  DependentBatch.typedInputOutputRatio BatchInputSlot BatchOutputPort
noncomputable def hh18OneLevelProtocolFamily
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    DistillationProtocolFamily QubitSpace PhysicalRegister LogicalRegister PUnit where
  targetError := fun _ =>
    (2 * residualCubicCoefficient) * epsilon.1 ^ 3
  protocol := fun _ => hh18MagicStateDistillationProtocol epsilon
  outputResourceCount := fun _ => 1
  outputResourceCount_pos := by
    intro _
    exact Nat.zero_lt_succ 0
  successfulOutputError_le_targetError := by
    intro _
    rw [hh18MagicStateDistillationProtocol_successfulOutputError]
    calc
      hh18OutputTraceError
          (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
          idealLogicalTOutput ≤ 2 * acceptedResidualError epsilon :=
        acceptedOutputTraceError_le_two_mul_acceptedResidual epsilon
      _ ≤ 2 * (residualCubicCoefficient * epsilon.1 ^ 3) :=
        mul_le_mul_of_nonneg_left
          (acceptedResidualError_le_cubic epsilon) (by norm_num)
      _ = (2 * residualCubicCoefficient) * epsilon.1 ^ 3 := by
        exact (mul_assoc _ _ _).symm
noncomputable def oneLevelFlaggedPool
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (count : Nat) :
    Fin count → DependentBatch.FiniteFlaggedBatch BatchOutputPort PhysicalErrorWord :=
  fun _ => oneLevelFlaggedBatch epsilon
abbrev depthTwoParentOutputSlots := Fin resourceCount × BatchOutputPort
abbrev depthTwoChildInputSlots := BatchOutputPort × Fin resourceCount
def depthTwoRouting : depthTwoParentOutputSlots ≃ depthTwoChildInputSlots :=
  DependentBatch.transposeRouting resourceCount 1
abbrev hh18DepthScheduleInputSlots (depth : Nat) := hh18DepthInputSlots depth
abbrev hh18DepthScheduleOutputSlots (depth : Nat) := hh18DepthOutputSlots depth
abbrev hh18DepthScheduleTargetError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat) : ℝ :=
  hh18CubicErrorEnvelope epsilon depth
abbrev hh18DepthScheduleActualOutputError
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : ℝ :=
  (hh18ErrorIteration epsilon hsmall depth).1
abbrev hh18DepthScheduleYieldFactor
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : hh18InitialSmallDomain epsilon) (depth : Nat) : NNReal :=
  hh18DepthYieldFactor epsilon hsmall depth
noncomputable def hh18DepthScheduleGamma : ℝ :=
  Real.log 15 / Real.log 3
noncomputable def hh18DepthScheduleLogGrowthBase
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  -Real.log (hh18IterationScale * epsilon.1)
noncomputable def hh18DepthScheduleCostCoefficient
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  2 / Real.rpow (hh18DepthScheduleLogGrowthBase epsilon)
    hh18DepthScheduleGamma
end HH18Protocol
end Distillation
end QEC


