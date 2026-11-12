-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:32:21.315135+00:00
-- url     : https://prove2.me/theorems/4b5222a5-52fa-4007-b1fd-bcccf0168ac9
-- title:
--   Path Envelope
-- statement:
--   Definitions and structural lemmas for Path Envelope, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_acceptedResidualError_le_sourceScaled
import Theorems.Thm_QEC_Distillation_HH18Parameterized_codeDistance_eq_binomialTail
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedErrorBranch_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_depthTwoRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_postselectionConditional_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_prepareMeasuredResources_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_residualCoefficient_nonneg
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildInputSlot_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildResources_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSuccessorRouting_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortComplementIdealState_apply
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortRawError_le_two_mul_acceptedResidual
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortTransport_apply_basis
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_erroredTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_idealTInvResourceUse_resource
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_adverse
import Theorems.Thm_QEC_Distillation_HH18PhaseInjection_tInvOutcomeCorrection_favorable
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
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedErrorBranch_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildInputSlot_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoChildResources_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.depthTwoRouting_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.postselectionConditional_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.prepareMeasuredResources_toOperator
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthChildResources_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.routedDepthSuccessorRouting_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
attribute [local simp] QEC.Distillation.HH18Parameterized.selectedLogicalPortTransport_apply_basis
attribute [local simp] QEC.Distillation.HH18PhaseInjection.erroredTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.idealTInvResourceUse_resource
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_adverse
attribute [local simp] QEC.Distillation.HH18PhaseInjection.tInvOutcomeCorrection_favorable
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
noncomputable def routedDepthRawErrorCoefficient (w r m : Nat) : ℝ :=
  2 * residualCoefficient w r m *
    (physicalInputCount m w : ℝ) ^ codeDistance r w
noncomputable def routedDepthIterationScale (w r m : Nat) : ℝ :=
  routedDepthRawErrorCoefficient w r m +
    2 * (physicalInputCount m w : ℝ) + 1
theorem routedDepthRawErrorCoefficient_nonneg (w r m : Nat) :
    0 ≤ routedDepthRawErrorCoefficient w r m := by
  unfold routedDepthRawErrorCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (residualCoefficient_nonneg w r m))
    (pow_nonneg (Nat.cast_nonneg _) _)
theorem routedDepthIterationScale_one_le (w r m : Nat) :
    1 ≤ routedDepthIterationScale w r m := by
  unfold routedDepthIterationScale
  linarith [routedDepthRawErrorCoefficient_nonneg w r m]
theorem routedDepthIterationScale_pos (w r m : Nat) :
    0 < routedDepthIterationScale w r m :=
  lt_of_lt_of_le zero_lt_one (routedDepthIterationScale_one_le w r m)
theorem codeDistance_two_le {w r m : Nat} (h : Admissible w r m) :
    2 ≤ codeDistance r w := by
  rcases h with ⟨_, hwr, _⟩
  rw [codeDistance_eq_binomialTail]
  change 2 ≤ ∑ i ∈ Finset.Icc (w + 1) (r + 1), Nat.choose (r + 1) i
  have hrpos : 0 < r := by
    omega
  have hsub : ({r, r + 1} : Finset Nat) ⊆ Finset.Icc (w + 1) (r + 1) := by
    intro index hindex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hindex
    rcases hindex with hindex | hindex
    · subst index
      simp
      omega
    · subst index
      simp
      omega
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun i => Nat.choose (r + 1) i) hsub
  calc
    2 ≤ (r + 1) + 1 := by omega
    _ = Nat.choose (r + 1) r + Nat.choose (r + 1) (r + 1) := by
      rw [Nat.choose_succ_self_right, Nat.choose_self]
    _ = ∑ i ∈ ({r, r + 1} : Finset Nat), Nat.choose (r + 1) i := by
      rw [Finset.sum_pair (Nat.ne_of_lt (Nat.lt_succ_self r))]
    _ ≤ ∑ i ∈ Finset.Icc (w + 1) (r + 1), Nat.choose (r + 1) i := hsum
theorem selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤
      routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w := by
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        2 * acceptedResidualError h hdegree rate :=
      selectedLogicalPortRawError_le_two_mul_acceptedResidual h hdegree rate port
    _ ≤ 2 * (residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * rate.1) ^ codeDistance r w) := by
      exact mul_le_mul_of_nonneg_left
        (acceptedResidualError_le_sourceScaled h hdegree rate) (by norm_num)
    _ = routedDepthRawErrorCoefficient w r m * rate.1 ^ codeDistance r w := by
      unfold routedDepthRawErrorCoefficient
      rw [mul_pow]
      ring
theorem routedDepthRawErrorCoefficient_le_scale_pow_pred {w r m : Nat}
    (h : Admissible w r m) :
    routedDepthRawErrorCoefficient w r m ≤
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) := by
  have hdistance : 2 ≤ codeDistance r w := codeDistance_two_le h
  have hone : 1 ≤ codeDistance r w - 1 := by
    omega
  calc
    routedDepthRawErrorCoefficient w r m ≤ routedDepthIterationScale w r m := by
      unfold routedDepthIterationScale
      linarith [routedDepthRawErrorCoefficient_nonneg w r m]
    _ = routedDepthIterationScale w r m ^ 1 := by simp
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) :=
      pow_le_pow_right₀ (routedDepthIterationScale_one_le w r m) hone
def routedDepthInitialSmallDomain (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  routedDepthIterationScale w r m * epsilon.1 ≤ 1 / 4
noncomputable def routedDepthErrorEnvelope (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Nat → ℝ
  | 0 => epsilon.1
  | depth + 1 =>
      routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
        (routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w
def routedDepthOutputPathInit (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthOutputSlots m w depth :=
  fun index => path index.castSucc
def routedDepthOutputPathLast (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) : LogicalSite m w :=
  path (Fin.last depth)
theorem routedDepthOutputPath_append_init_last (m w depth : Nat)
    (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthOutputPathAppend m w depth
      (routedDepthOutputPathInit m w depth path)
      (routedDepthOutputPathLast m w depth path) = path := by
  funext index
  refine Fin.lastCases ?_ ?_ index
  · simp [routedDepthOutputPathAppend, routedDepthOutputPathLast]
  · intro prefixIndex
    simp [routedDepthOutputPathAppend, routedDepthOutputPathInit]
@[simp] theorem routedDepthOutputPathInit_append (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputPathInit m w depth
      (routedDepthOutputPathAppend m w depth path port) = path := by
  funext index
  simp [routedDepthOutputPathInit, routedDepthOutputPathAppend]
@[simp] theorem routedDepthOutputPathLast_append (m w depth : Nat)
    (path : routedDepthOutputSlots m w depth) (port : LogicalSite m w) :
    routedDepthOutputPathLast m w depth
      (routedDepthOutputPathAppend m w depth path port) = port :=
  by
    simp [routedDepthOutputPathLast, routedDepthOutputPathAppend]
structure RoutedDepthPathIteration {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) where
  rate : HH18NoisyInput.DiagonalErrorRate
  state : RoutedDepthState h hdegree epsilon depth path rate
  scaled_small : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4
  rate_le_envelope : rate.1 ≤ routedDepthErrorEnvelope w r m epsilon depth
theorem routedDepthIteration_scale_mul_rawError_le_quarter
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 4 := by
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree current.rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ current.rate.1 := current.rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hscaledPower :
      (routedDepthIterationScale w r m * current.rate.1) ^ codeDistance r w ≤
        (1 / 4 : ℝ) ^ codeDistance r w :=
    pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg)
      current.scaled_small _
  calc
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthIterationScale w r m *
          (routedDepthRawErrorCoefficient w r m *
            current.rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left hraw hscaleNonneg
    _ ≤ routedDepthIterationScale w r m *
          (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            current.rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdomination
          (pow_nonneg hrateNonneg _)) hscaleNonneg
    _ = (routedDepthIterationScale w r m * current.rate.1) ^ codeDistance r w := by
      rw [mul_pow]
      have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
        Nat.sub_add_cancel hdistance
      calc
        routedDepthIterationScale w r m *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              current.rate.1 ^ codeDistance r w) =
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthIterationScale w r m) *
              current.rate.1 ^ codeDistance r w := by ring
        _ = routedDepthIterationScale w r m ^ codeDistance r w *
              current.rate.1 ^ codeDistance r w := by
          rw [← pow_succ, hsub]
    _ ≤ (1 / 4 : ℝ) ^ codeDistance r w := hscaledPower
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdistance
    _ = 1 / 4 := by norm_num
theorem routedDepthIteration_next_half
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 2 := by
  have hrawNonneg : 0 ≤ selectedLogicalPortRawError h hdegree current.rate port :=
    selectedLogicalPortRawError_nonneg h hdegree current.rate port
  have hscaled := routedDepthIteration_scale_mul_rawError_le_quarter
    h hdegree epsilon hsmall current port
  have hscaleOne : 1 ≤ routedDepthIterationScale w r m :=
    routedDepthIterationScale_one_le w r m
  calc
    selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthIterationScale w r m *
          selectedLogicalPortRawError h hdegree current.rate port := by
      nlinarith
    _ ≤ 1 / 4 := hscaled
    _ ≤ 1 / 2 := by norm_num
theorem routedDepthIteration_next_scaled_small
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        (selectedLogicalPortNextInputRate h hdegree current.rate port
          (routedDepthIteration_next_half h hdegree epsilon hsmall current port)).1 ≤ 1 / 4 := by
  change routedDepthIterationScale w r m *
      selectedLogicalPortRawError h hdegree current.rate port ≤ 1 / 4
  exact routedDepthIteration_scale_mul_rawError_le_quarter
    h hdegree epsilon hsmall current port
theorem routedDepthIteration_next_le_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} {path : routedDepthOutputSlots m w depth}
    (current : RoutedDepthPathIteration h hdegree epsilon hsmall depth path)
    (port : LogicalSite m w) :
    (selectedLogicalPortNextInputRate h hdegree current.rate port
      (routedDepthIteration_next_half h hdegree epsilon hsmall current port)).1 ≤
        routedDepthErrorEnvelope w r m epsilon (depth + 1) := by
  change selectedLogicalPortRawError h hdegree current.rate port ≤ _
  calc
    selectedLogicalPortRawError h hdegree current.rate port ≤
        routedDepthRawErrorCoefficient w r m * current.rate.1 ^ codeDistance r w :=
      selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
        h hdegree current.rate port
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          current.rate.1 ^ codeDistance r w :=
      mul_le_mul_of_nonneg_right
        (routedDepthRawErrorCoefficient_le_scale_pow_pred h)
        (pow_nonneg current.rate.property.1 _)
    _ ≤ routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
          (routedDepthErrorEnvelope w r m epsilon depth) ^ codeDistance r w :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ current.rate.property.1 current.rate_le_envelope _)
        (pow_nonneg (routedDepthIterationScale_pos w r m).le _)
    _ = routedDepthErrorEnvelope w r m epsilon (depth + 1) := rfl
noncomputable def routedDepthPathIteration {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → (path : routedDepthOutputSlots m w depth) →
      RoutedDepthPathIteration h hdegree epsilon hsmall depth path
  | 0, path => by
      have hpath : path = routedDepthOutputPathEmpty m w := Subsingleton.elim _ _
      subst path
      exact ⟨epsilon, RoutedDepthState.root, hsmall, by rfl⟩
  | depth + 1, path => by
      let previous := routedDepthPathIteration h hdegree epsilon hsmall depth
        (routedDepthOutputPathInit m w depth path)
      let port := routedDepthOutputPathLast m w depth path
      let hhalf := routedDepthIteration_next_half h hdegree epsilon hsmall previous port
      refine ⟨selectedLogicalPortNextInputRate h hdegree previous.rate port hhalf, ?_,
        routedDepthIteration_next_scaled_small h hdegree epsilon hsmall previous port,
        routedDepthIteration_next_le_envelope h hdegree epsilon hsmall previous port⟩
      have hstate := RoutedDepthState.succ previous.state port hhalf
      simpa only [port, routedDepthOutputPath_append_init_last] using hstate
noncomputable def routedDepthStateProjectionRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    HH18NoisyInput.DiagonalErrorRate :=
  (routedDepthPathIteration h hdegree epsilon hsmall depth path).rate
noncomputable def routedDepthStateProjection {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    RoutedDepthState h hdegree epsilon depth path
      (routedDepthStateProjectionRate h hdegree epsilon hsmall depth path) :=
  (routedDepthPathIteration h hdegree epsilon hsmall depth path).state
theorem routedDepthScale_mul_selectedRawError_le_quarter
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree rate port ≤ 1 / 4 := by
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hraw := selectedLogicalPortRawError_le_routedDepthRawErrorCoefficient_mul_pow
    h hdegree rate port
  have hdomination := routedDepthRawErrorCoefficient_le_scale_pow_pred h
  have hrateNonneg : 0 ≤ rate.1 := rate.property.1
  have hscaleNonneg : 0 ≤ routedDepthIterationScale w r m :=
    (routedDepthIterationScale_pos w r m).le
  have hscaledPower :
      (routedDepthIterationScale w r m * rate.1) ^ codeDistance r w ≤
        (1 / 4 : ℝ) ^ codeDistance r w :=
    pow_le_pow_left₀ (mul_nonneg hscaleNonneg hrateNonneg) hscaled _
  calc
    routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthIterationScale w r m *
          (routedDepthRawErrorCoefficient w r m *
            rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left hraw hscaleNonneg
    _ ≤ routedDepthIterationScale w r m *
          (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
            rate.1 ^ codeDistance r w) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdomination
          (pow_nonneg hrateNonneg _)) hscaleNonneg
    _ = (routedDepthIterationScale w r m * rate.1) ^ codeDistance r w := by
      rw [mul_pow]
      have hsub : codeDistance r w - 1 + 1 = codeDistance r w :=
        Nat.sub_add_cancel hdistance
      calc
        routedDepthIterationScale w r m *
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              rate.1 ^ codeDistance r w) =
            (routedDepthIterationScale w r m ^ (codeDistance r w - 1) *
              routedDepthIterationScale w r m) *
              rate.1 ^ codeDistance r w := by ring
        _ = routedDepthIterationScale w r m ^ codeDistance r w *
              rate.1 ^ codeDistance r w := by
          rw [← pow_succ, hsub]
    _ ≤ (1 / 4 : ℝ) ^ codeDistance r w := hscaledPower
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdistance
    _ = 1 / 4 := by norm_num
theorem routedDepthSelectedRawError_half_of_scaled
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate)
    (hscaled : routedDepthIterationScale w r m * rate.1 ≤ 1 / 4)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2 := by
  have hrawNonneg : 0 ≤ selectedLogicalPortRawError h hdegree rate port :=
    selectedLogicalPortRawError_nonneg h hdegree rate port
  have hscaleOne : 1 ≤ routedDepthIterationScale w r m :=
    routedDepthIterationScale_one_le w r m
  calc
    selectedLogicalPortRawError h hdegree rate port ≤
        routedDepthIterationScale w r m *
          selectedLogicalPortRawError h hdegree rate port := by
      nlinarith
    _ ≤ 1 / 4 :=
      routedDepthScale_mul_selectedRawError_le_quarter h hdegree rate hscaled port
    _ ≤ 1 / 2 := by norm_num
noncomputable def routedDepthTotalNextInputRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    HH18NoisyInput.DiagonalErrorRate :=
  dite (selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2)
    (fun hhalf => selectedLogicalPortNextInputRate h hdegree rate port hhalf)
    (fun _ => rate)
theorem routedDepthTotalNextInputRate_of_half {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (rate : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree rate port ≤ 1 / 2) :
    routedDepthTotalNextInputRate h hdegree rate port =
      selectedLogicalPortNextInputRate h hdegree rate port hhalf := by
  have hhalf' : selectedLogicalPortRawError h hdegree rate port ≤ (2 : ℝ)⁻¹ := by
    simpa using hhalf
  simp [routedDepthTotalNextInputRate, hhalf']
noncomputable def routedDepthPathRate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (_hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → routedDepthOutputSlots m w depth →
      HH18NoisyInput.DiagonalErrorRate
  | 0, _ => epsilon
  | depth + 1, path =>
      routedDepthTotalNextInputRate h hdegree
        (routedDepthPathRate h hdegree epsilon _hsmall depth
          (routedDepthOutputPathInit m w depth path))
        (routedDepthOutputPathLast m w depth path)
@[simp] theorem routedDepthPathRate_root {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (path : routedDepthOutputSlots m w 0) :
    routedDepthPathRate h hdegree epsilon hsmall 0 path = epsilon :=
  rfl
@[simp] theorem routedDepthPathRate_succ {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w (depth + 1)) :
    routedDepthPathRate h hdegree epsilon hsmall (depth + 1) path =
      routedDepthTotalNextInputRate h hdegree
        (routedDepthPathRate h hdegree epsilon hsmall depth
          (routedDepthOutputPathInit m w depth path))
        (routedDepthOutputPathLast m w depth path) :=
  rfl
theorem routedDepthPathRate_scaled_small {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    ∀ (depth : Nat) (path : routedDepthOutputSlots m w depth),
      routedDepthIterationScale w r m *
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤ 1 / 4 := by
  intro depth
  induction depth with
  | zero =>
      intro path
      simpa [routedDepthInitialSmallDomain] using hsmall
  | succ depth ih =>
      intro path
      let previous := routedDepthPathRate h hdegree epsilon hsmall depth
        (routedDepthOutputPathInit m w depth path)
      let port := routedDepthOutputPathLast m w depth path
      have hprevious : routedDepthIterationScale w r m * previous.1 ≤ 1 / 4 :=
        ih (routedDepthOutputPathInit m w depth path)
      have hhalf : selectedLogicalPortRawError h hdegree previous port ≤ 1 / 2 :=
        routedDepthSelectedRawError_half_of_scaled h hdegree previous hprevious port
      rw [routedDepthPathRate_succ,
        routedDepthTotalNextInputRate_of_half h hdegree previous port hhalf]
      change routedDepthIterationScale w r m *
        selectedLogicalPortRawError h hdegree previous port ≤ 1 / 4
      exact routedDepthScale_mul_selectedRawError_le_quarter
        h hdegree previous hprevious port
theorem routedDepthPathNextHalf {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    selectedLogicalPortRawError h hdegree
      (routedDepthPathRate h hdegree epsilon hsmall depth path) port ≤ 1 / 2 :=
  routedDepthSelectedRawError_half_of_scaled h hdegree
    (routedDepthPathRate h hdegree epsilon hsmall depth path)
    (routedDepthPathRate_scaled_small h hdegree epsilon hsmall depth path) port
noncomputable def routedDepthPathState {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    (depth : Nat) → (path : routedDepthOutputSlots m w depth) →
      RoutedDepthState h hdegree epsilon depth path
        (routedDepthPathRate h hdegree epsilon hsmall depth path)
  | 0, path => by
      have hpath : path = routedDepthOutputPathEmpty m w := Subsingleton.elim _ _
      subst path
      exact RoutedDepthState.root
  | depth + 1, path => by
      let priorPath := routedDepthOutputPathInit m w depth path
      let port := routedDepthOutputPathLast m w depth path
      let hhalf := routedDepthPathNextHalf h hdegree epsilon hsmall priorPath port
      have hrate : routedDepthPathRate h hdegree epsilon hsmall (depth + 1) path =
          selectedLogicalPortNextInputRate h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall depth priorPath) port hhalf := by
        rw [routedDepthPathRate_succ,
          routedDepthTotalNextInputRate_of_half h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall depth priorPath) port hhalf]
      rw [hrate]
      have hstate := RoutedDepthState.succ
        (routedDepthPathState h hdegree epsilon hsmall depth priorPath) port hhalf
      simpa only [priorPath, port, routedDepthOutputPath_append_init_last] using hstate
structure RoutedDepthPathStatePackage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) where
  rate : HH18NoisyInput.DiagonalErrorRate
  state : RoutedDepthState h hdegree epsilon depth path rate
noncomputable def routedDepthPathStatePackage {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
  (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    RoutedDepthPathStatePackage h hdegree epsilon hsmall depth path := by
  exact ⟨routedDepthPathRate h hdegree epsilon hsmall depth path,
    routedDepthPathState h hdegree epsilon hsmall depth path⟩
noncomputable def routedDepthPathActualRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  resourceDecodedRun h hdegree (noisyResources m w
    (routedDepthPathRate h hdegree epsilon hsmall depth path))
end HH18Parameterized
end Distillation
end QEC


