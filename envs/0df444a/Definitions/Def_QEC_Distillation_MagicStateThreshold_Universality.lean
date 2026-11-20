-- Prove2me | Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
-- name    : QEC_Distillation_MagicStateThreshold_Universality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T21:28:40.091152+00:00
-- url     : https://prove2.me/theorems/d377d6c7-42f5-41ce-87b8-e6563e30db02
-- title:
--   Universality
-- statement:
--   Definitions and structural lemmas for Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_IdealResourceUniversality
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_branchOperator
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
import Theorems.Thm_QEC_Distillation_BK05T_bk05TIteration_nonneg_and_lt_threshold
import Theorems.Thm_QEC_Distillation_BK05T_bk05TIteration_zero
import Theorems.Thm_QEC_Distillation_BK05T_bk05TThreshold_lt_half
import Definitions.Def_QECert_BK05T_AcceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15IterationEpsilon_error
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_zero
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_compose
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_identity
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_oneQubit
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_FiniteRegisterCircuit_unitary_xor
import Theorems.Thm_QEC_Distillation_FiniteRegisterUniversality_registerXorGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngle_cos
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseInverseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
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
import Theorems.Thm_QEC_Distillation_phaseNormalize_matrix
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_exists_finiteKrausFamily_representation
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_ThermalEncoding_prepareRight_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_stdChoiMatrix_posSemidef_of_completelyPositive
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
private theorem qecert_bk05tIteration_zero_simp_compat (epsilon : Real) :
    QEC.Distillation.BK05T.bk05TIteration epsilon 0 = epsilon :=
  QEC.Distillation.BK05T.bk05TIteration_zero epsilon
attribute [local simp] qecert_bk05tIteration_zero_simp_compat
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
attribute [local simp] QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error
attribute [local simp] QEC.Distillation.BK15.Threshold.bk15Iteration_zero
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_compose
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_identity
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_oneQubit
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.FiniteRegisterCircuit.unitary_xor
attribute [local simp] QEC.Distillation.FiniteRegisterUniversality.registerXorGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.hAngle_cos
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseInverseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
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
attribute [local simp] QEC.Distillation.phaseNormalize_matrix
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
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
universe u v
namespace QEC
namespace Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise
abbrev tInitialError (rho : DensityOperator QubitSpace) : Real :=
  BK05T.bk05TFidelityError rho
abbrev tIteration (rho : DensityOperator QubitSpace) (rounds : Nat) : Real :=
  BK05T.bk05TIteration (tInitialError rho) rounds
inductive BK05TSemanticSchedule (rho : DensityOperator QubitSpace) : Nat -> Type
  | leaf (resource : DensityOperator QubitSpace) : BK05TSemanticSchedule rho 0
  | accepted {depth : Nat}
      (children : Fin 5 -> BK05TSemanticSchedule rho depth)
      (acceptedOutput : DensityOperator QubitSpace) :
      BK05TSemanticSchedule rho (depth + 1)
namespace BK05TSemanticSchedule
def leafCount {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK05TSemanticSchedule rho depth -> Nat
  | _, .leaf _ => 1
  | _, .accepted children _ => Finset.univ.sum fun site => leafCount (children site)
def rootOutput {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK05TSemanticSchedule rho depth -> DensityOperator QubitSpace
  | _, .leaf resource => resource
  | _, .accepted _ acceptedOutput => acceptedOutput
def rootInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK05TSemanticSchedule rho (depth + 1)) :
    ResourceInput 5 QubitSpace :=
  match schedule with
  | .accepted children _ => fun site => rootOutput (children site)
noncomputable def preparedInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK05TSemanticSchedule rho (depth + 1)) :
    DensityOperator BK05T.FiveQubitSpace :=
  BK05T.fiveQubitPrepareInput (rootInput schedule)
end BK05TSemanticSchedule
theorem tIteration_bounds
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    0 <= tIteration rho rounds /\ tIteration rho rounds <= 1 / 2 := by
  have h := BK05T.bk05TIteration_nonneg_and_lt_threshold
    (tInitialError rho) (BK05T.bk05TFidelityError_nonneg rho) hthreshold rounds
  exact ⟨h.1, (h.2.trans BK05T.bk05TThreshold_lt_half).le⟩
theorem tIteration_le_one
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    tIteration rho rounds <= 1 :=
  (tIteration_bounds rho hthreshold rounds).2.trans (by norm_num)
noncomputable def bk05TCompleteSemanticSchedule
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) :
    (rounds : Nat) -> BK05TSemanticSchedule rho rounds
  | 0 => .leaf (BK05T.tTwirl (BK05T.tCanonicalizedInput rho))
  | depth + 1 => .accepted
      (fun _ => bk05TCompleteSemanticSchedule rho hthreshold depth)
      (BK05T.QECertAcceptedOutput.fiveQubitAcceptedOutput (tIteration rho depth)
        (tIteration_bounds rho hthreshold depth).1
        (tIteration_le_one rho hthreshold depth))
def hOrthogonalPart (u : QubitSpace) : QubitSpace :=
  u - inner Complex sourceHState u • sourceHState
open AdaptiveIdealClifford PhaseInjection
inductive BK05ResourceToken
  | h
  | t
deriving DecidableEq
inductive BK05RawLeafKind
  | targetHit
  | phaseExhausted
  | tPairExhausted
deriving DecidableEq
structure BK05RawLeaf where
  kind : BK05RawLeafKind
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator QubitSpace
def rawWeight (leaf : BK05RawLeaf) : Real :=
  (LinearMap.trace Complex QubitSpace leaf.raw).re
def rawMass (leaves : List BK05RawLeaf) : Real :=
  (leaves.map rawWeight).sum
def rawAggregate (leaves : List BK05RawLeaf) : Operator QubitSpace :=
  (leaves.map BK05RawLeaf.raw).sum
def rawMassOfKind (kind : BK05RawLeafKind) (leaves : List BK05RawLeaf) : Real :=
  rawMass (leaves.filter fun leaf => leaf.kind == kind)
def injectedInputRaw (data resource : Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport.conjOperator
    (TensorProduct.map data resource)
def phaseBranchRaw (resource data : Operator QubitSpace) (coin : Bool) :
    Operator QubitSpace :=
  oneShotPostprocess
    (zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
      (injectedInputRaw data resource))
def hPhaseRaw (h : DensityOperator QubitSpace) : Operator QubitSpace :=
  hResourceTransport.conjOperator h.toOperator
def hStepRaw (h : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) : Operator QubitSpace :=
  phaseBranchRaw (hPhaseRaw h) data coin
def tPairInputRaw (t : DensityOperator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport.conjOperator
    (TensorProduct.map t.toOperator t.toOperator)
def tPairBranchRaw (t : DensityOperator QubitSpace) (coin : Bool) :
    Operator TwoQubit.TwoQubitSpace :=
  zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
    (tPairInputRaw t)
def tAcceptedPhaseRaw (t : DensityOperator QubitSpace) : Operator QubitSpace :=
  (QuantumChannel.unitaryConj hadamardTransport)
    (oneShotPostprocess (tPairBranchRaw t true))
def tRejectedDataRaw (data : Operator QubitSpace)
    (t : DensityOperator QubitSpace) : Operator QubitSpace :=
  partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
    (TensorProduct.map data (tPairBranchRaw t false))
def hRetry {q : Nat} (h : DensityOperator QubitSpace) (target : ZMod q)
    (remaining : Nat) (position : ZMod q)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05RawLeaf :=
  if position = target then
    [⟨.targetHit, history, ledger, data⟩]
  else match remaining with
  | 0 => [⟨.phaseExhausted, history, ledger, data⟩]
  | n + 1 =>
      let nextLedger := ledger + ({.h} : ResourceLedger BK05ResourceToken)
      hRetry h target n (position + 1) nextLedger (true :: history)
          (hStepRaw h true data)
        ++
      hRetry h target n (position - 1) nextLedger (false :: history)
          (hStepRaw h false data)
termination_by remaining
inductive BK05TSupplyOutcome where
  | accepted (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data phaseResource : Operator QubitSpace) : BK05TSupplyOutcome
  | exhausted (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
      (data : Operator QubitSpace) : BK05TSupplyOutcome
def tSupply (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05TSupplyOutcome :=
  match pairAttempts with
  | 0 => [.exhausted ledger history data]
  | m + 1 =>
      let nextLedger := ledger + ({.t, .t} : ResourceLedger BK05ResourceToken)
      .accepted nextLedger (true :: history) data (tAcceptedPhaseRaw t)
        ::
      tSupply t m nextLedger (false :: history) (tRejectedDataRaw data t)
termination_by pairAttempts
def tRetry {q : Nat} (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (target : ZMod q) (remaining : Nat) (position : ZMod q)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05RawLeaf :=
  if position = target then
    [⟨.targetHit, history, ledger, data⟩]
  else match remaining with
  | 0 => [⟨.phaseExhausted, history, ledger, data⟩]
  | n + 1 =>
      (tSupply t pairAttempts ledger history data).flatMap fun supplied =>
        match supplied with
        | .accepted nextLedger nextHistory nextData phaseResource =>
            tRetry t pairAttempts target n (position + 1) nextLedger
                (true :: nextHistory) (phaseBranchRaw phaseResource nextData true)
              ++
            tRetry t pairAttempts target n (position - 1) nextLedger
                (false :: nextHistory) (phaseBranchRaw phaseResource nextData false)
        | .exhausted nextLedger nextHistory nextData =>
            [⟨.tPairExhausted, nextHistory, nextLedger, nextData⟩]
termination_by remaining
def hActualRawTree (h : DensityOperator QubitSpace) (target : ZMod 8)
    (blocks : Nat) (rho : DensityOperator QubitSpace) : List BK05RawLeaf :=
  hRetry h target (8 * blocks) 0 0 [] rho.toOperator
def tActualRawTree (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (target : ZMod 12) (blocks : Nat) (rho : DensityOperator QubitSpace) :
    List BK05RawLeaf :=
  tRetry t pairAttempts target (12 * blocks) 0 0 [] rho.toOperator
def tSupplyWeight : BK05TSupplyOutcome → Complex
  | .accepted _ _ data phaseResource =>
      LinearMap.trace Complex QubitSpace data *
        LinearMap.trace Complex QubitSpace phaseResource
  | .exhausted _ _ data => LinearMap.trace Complex QubitSpace data
def tSupplyMass (outcomes : List BK05TSupplyOutcome) : Complex :=
  (outcomes.map tSupplyWeight).sum
theorem injectedInputRaw_add (data₁ data₂ resource : Operator QubitSpace) :
    injectedInputRaw (data₁ + data₂) resource =
      injectedInputRaw data₁ resource + injectedInputRaw data₂ resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_add_left]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_add _ _
theorem injectedInputRaw_smul (scalar : Complex) (data resource : Operator QubitSpace) :
    injectedInputRaw (scalar • data) resource =
      scalar • injectedInputRaw data resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_smul_left]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_smul scalar _
noncomputable def phaseBranchRawLinear (resource : Operator QubitSpace)
    (coin : Bool) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun data => phaseBranchRaw resource data coin
  map_add' := by
    intro data₁ data₂
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_add]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    rw [← map_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' := by
    intro scalar data
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_smul]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← map_smul]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
def hExhaustionCoeff (target : ZMod 8) : Nat → ZMod 8 → Real
  | 0, position => if position = target then 0 else 1
  | remaining + 1, position =>
      if position = target then 0 else
        (hExhaustionCoeff target remaining (position + 1) +
          hExhaustionCoeff target remaining (position - 1)) / 2
theorem injectedInputRaw_add_right
    (data resource₁ resource₂ : Operator QubitSpace) :
    injectedInputRaw data (resource₁ + resource₂) =
      injectedInputRaw data resource₁ + injectedInputRaw data resource₂ := by
  unfold injectedInputRaw
  rw [TensorProduct.map_add_right]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_add _ _
theorem injectedInputRaw_smul_right
    (scalar : Complex) (data resource : Operator QubitSpace) :
    injectedInputRaw data (scalar • resource) =
      scalar • injectedInputRaw data resource := by
  unfold injectedInputRaw
  rw [TensorProduct.map_smul_right]
  exact TwoQubit.tensorRegisterTransport.conjOperatorLinearMap.map_smul scalar _
noncomputable def phaseBranchRawResourceLinear
    (data : Operator QubitSpace) (coin : Bool) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun resource => phaseBranchRaw resource data coin
  map_add' := by
    intro resource₁ resource₂
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_add_right]
    simp only [LinearMap.comp_add, LinearMap.add_comp]
    rw [← map_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' := by
    intro scalar resource
    classical
    unfold phaseBranchRaw FiniteInstrument.branchOperator
    rw [injectedInputRaw_smul_right]
    simp only [LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← map_smul]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
def tSupplyExhaustedMass (outcomes : List BK05TSupplyOutcome) : Real :=
  (outcomes.map fun outcome =>
    match outcome with
    | .accepted _ _ _ _ => 0
    | .exhausted _ _ data => (LinearMap.trace Complex QubitSpace data).re).sum
def tSupplyAcceptedPhaseMass (coin : Bool)
    (outcomes : List BK05TSupplyOutcome) : Real :=
  (outcomes.map fun outcome =>
    match outcome with
    | .accepted _ _ data phaseResource =>
        (LinearMap.trace Complex QubitSpace
          (phaseBranchRaw phaseResource data coin)).re
    | .exhausted _ _ _ => 0).sum
def tPhaseExhaustionCoeff (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Real
  | 0, position => if position = target then 0 else 1
  | remaining + 1, position =>
      if position = target then 0 else
        ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
          (tPhaseExhaustionCoeff pairAttempts target remaining (position + 1) +
            tPhaseExhaustionCoeff pairAttempts target remaining (position - 1))
noncomputable def hRetryAggregateLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _ => LinearMap.id
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        (hRetryAggregateLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryAggregateLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)
noncomputable def observedBranchLinear (coin : Bool) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator TwoQubit.TwoQubitSpace where
  toFun := fun input =>
    zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin) input
  map_add' := by
    intro input₁ input₂
    classical
    unfold FiniteInstrument.branchOperator
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' := by
    intro scalar input
    classical
    unfold FiniteInstrument.branchOperator
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [LinearMap.comp_smul, LinearMap.smul_comp]
theorem observedBranchLinear_apply (coin : Bool)
    (input : Operator TwoQubit.TwoQubitSpace) :
    observedBranchLinear coin input =
      zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin) input :=
  rfl
noncomputable def phaseContinuationLinear
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  nextTrue.comp (oneShotPostprocess.toLinearMap.comp (observedBranchLinear true)) +
    nextFalse.comp (oneShotPostprocess.toLinearMap.comp (observedBranchLinear false))
noncomputable def tPairRejectedDataLinear (data : Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun pair =>
    partialTraceRightRaw QubitSpace TwoQubit.TwoQubitSpace
      (TensorProduct.map data pair)
  map_add' := by
    intro pair₁ pair₂
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map data (pair₁ + pair₂)) = _
    rw [TensorProduct.map_add_right]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_add _ _
  map_smul' := by
    intro scalar pair
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map data (scalar • pair)) = _
    rw [TensorProduct.map_smul_right]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_smul _ _
noncomputable def tPairAcceptedPhaseLinear :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  (QuantumChannel.unitaryConj hadamardTransport).toLinearMap.comp
    (oneShotPostprocess.toLinearMap.comp (observedBranchLinear true))
noncomputable def tPairContinuationLinear
    (data : Operator QubitSpace)
    (nextTrue nextFalse onReject : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator TwoQubit.TwoQubitSpace →ₗ[Complex] Operator QubitSpace :=
  nextTrue.comp ((phaseBranchRawResourceLinear data true).comp tPairAcceptedPhaseLinear) +
    nextFalse.comp ((phaseBranchRawResourceLinear data false).comp tPairAcceptedPhaseLinear) +
    onReject.comp ((tPairRejectedDataLinear data).comp (observedBranchLinear false))
noncomputable def tRejectedDataRawLinear (t : DensityOperator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := fun data => tRejectedDataRaw data t
  map_add' := by
    intro data₁ data₂
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map (data₁ + data₂) (tPairBranchRaw t false)) = _
    rw [TensorProduct.map_add_left]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_add _ _
  map_smul' := by
    intro scalar data
    change (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap
        (TensorProduct.map (scalar • data) (tPairBranchRaw t false)) = _
    rw [TensorProduct.map_smul_left]
    exact (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace).toLinearMap.map_smul _ _
noncomputable def tSupplyAggregateLinear
    (t : DensityOperator QubitSpace) : Nat →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _, _ => LinearMap.id
  | attempts + 1, nextTrue, nextFalse =>
      nextTrue.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) true) +
        nextFalse.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) false) +
        (tSupplyAggregateLinear t attempts nextTrue nextFalse).comp
          (tRejectedDataRawLinear t)
noncomputable def tRetryAggregateLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _ => LinearMap.id
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        tSupplyAggregateLinear t pairAttempts
          (tRetryAggregateLinear t pairAttempts target remaining (position + 1))
          (tRetryAggregateLinear t pairAttempts target remaining (position - 1))
def tSupplyAggregateValue
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    List BK05TSupplyOutcome → Operator QubitSpace
  | [] => 0
  | .accepted _ _ data phaseResource :: outcomes =>
      nextTrue (phaseBranchRaw phaseResource data true) +
        nextFalse (phaseBranchRaw phaseResource data false) +
        tSupplyAggregateValue nextTrue nextFalse outcomes
  | .exhausted _ _ data :: outcomes =>
      data + tSupplyAggregateValue nextTrue nextFalse outcomes
inductive BK05GeneratorWord
    (generators : Set (UnitaryGate (Fin 2))) : Type
  | one : BK05GeneratorWord generators
  | generator (gate : UnitaryGate (Fin 2))
      (hgate : gate ∈ generators) : BK05GeneratorWord generators
  | mul (left right : BK05GeneratorWord generators) :
      BK05GeneratorWord generators
  | inverse (word : BK05GeneratorWord generators) :
      BK05GeneratorWord generators
noncomputable def BK05GeneratorWord.eval
    {generators : Set (UnitaryGate (Fin 2))} :
    BK05GeneratorWord generators → UnitaryGate (Fin 2)
  | .one => 1
  | .generator gate _ => gate
  | .mul left right => left.eval * right.eval
  | .inverse word => word.eval⁻¹
inductive BK05WordPolarity where
  | normal | inverse
def BK05WordPolarity.flip : BK05WordPolarity → BK05WordPolarity
  | .normal => .inverse
  | .inverse => .normal
noncomputable def BK05GeneratorWord.orientedEval
    {generators : Set (UnitaryGate (Fin 2))}
    (word : BK05GeneratorWord generators) :
    BK05WordPolarity → UnitaryGate (Fin 2)
  | .normal => word.eval
  | .inverse => word.eval⁻¹
noncomputable def BK05GeneratorWord.compileAt
    {generators : Set (UnitaryGate (Fin 2))}
    {Wire : Type u} [Fintype Wire] [DecidableEq Wire] (wire : Wire) :
    (word : BK05GeneratorWord generators) → BK05WordPolarity →
      FiniteRegisterCircuit Wire
  | .one, _ => .identity
  | .generator gate _, .normal => .oneQubit wire gate
  | .generator gate _, .inverse => .oneQubit wire gate⁻¹
  | .mul left right, .normal =>
      .compose (right.compileAt wire .normal) (left.compileAt wire .normal)
  | .mul left right, .inverse =>
      .compose (left.compileAt wire .inverse) (right.compileAt wire .inverse)
  | .inverse word, polarity => word.compileAt wire polarity.flip
inductive BK05PhaseAtom (theta : Real) : Type
  | h
  | k
  | phase
noncomputable def BK05PhaseAtom.eval (theta : Real) :
    BK05PhaseAtom theta → UnitaryGate (Fin 2)
  | .h => hadamardGate
  | .k => phaseGate
  | .phase => phaseShiftGate theta
inductive BK05SignedPhaseLetter (theta : Real) : Type
  | positive (atom : BK05PhaseAtom theta)
  | negative (atom : BK05PhaseAtom theta)
noncomputable def BK05SignedPhaseLetter.eval (theta : Real) :
    BK05SignedPhaseLetter theta → UnitaryGate (Fin 2)
  | .positive atom => atom.eval theta
  | .negative atom => (atom.eval theta)⁻¹
def BK05SignedPhaseLetter.phaseCost (theta : Real) :
    BK05SignedPhaseLetter theta → Nat
  | .positive .phase => 1
  | .negative .phase => 1
  | _ => 0
theorem exists_phaseAtom_eq_of_mem
    (theta : Real) (gate : UnitaryGate (Fin 2))
    (hgate : gate ∈ cliffordPhaseGenerators theta) :
    ∃ atom : BK05PhaseAtom theta, atom.eval theta = gate := by
  simp only [cliffordPhaseGenerators, Set.mem_insert_iff, Set.mem_singleton_iff]
    at hgate
  rcases hgate with hgate | hgate | hgate
  · exact ⟨.h, hgate.symm⟩
  · exact ⟨.k, hgate.symm⟩
  · exact ⟨.phase, hgate.symm⟩
noncomputable def reifyPhaseAtom
    (theta : Real) (gate : UnitaryGate (Fin 2))
    (hgate : gate ∈ cliffordPhaseGenerators theta) :
    {atom : BK05PhaseAtom theta // atom.eval theta = gate} :=
  ⟨Classical.choose (exists_phaseAtom_eq_of_mem theta gate hgate),
    Classical.choose_spec (exists_phaseAtom_eq_of_mem theta gate hgate)⟩
noncomputable def BK05GeneratorWord.normalizeSigned
    (theta : Real) :
    BK05WordPolarity →
    BK05GeneratorWord (cliffordPhaseGenerators theta) →
      List (BK05SignedPhaseLetter theta)
  | .normal, .one => []
  | .inverse, .one => []
  | .normal, .generator gate hgate =>
      [.positive (reifyPhaseAtom theta gate hgate).1]
  | .inverse, .generator gate hgate =>
      [.negative (reifyPhaseAtom theta gate hgate).1]
  | .normal, .mul left right =>
      left.normalizeSigned theta .normal ++ right.normalizeSigned theta .normal
  | .inverse, .mul left right =>
      right.normalizeSigned theta .inverse ++ left.normalizeSigned theta .inverse
  | polarity, .inverse word => word.normalizeSigned theta polarity.flip
noncomputable def BK05SignedPhaseLetter.evalList (theta : Real) :
    List (BK05SignedPhaseLetter theta) → UnitaryGate (Fin 2)
  | [] => 1
  | letter :: tail => letter.eval theta * evalList theta tail
def BK05SignedPhaseLetter.resourceCount (theta : Real) :
    List (BK05SignedPhaseLetter theta) → Nat
  | [] => 0
  | letter :: tail => letter.phaseCost theta + resourceCount theta tail
noncomputable def BK05GeneratorWord.phaseLetterCount
    (theta : Real)
    (word : BK05GeneratorWord (cliffordPhaseGenerators theta)) : Nat :=
  BK05SignedPhaseLetter.resourceCount theta
    (word.normalizeSigned theta .normal)
inductive BK05WordLeafStatus where
  | live
  | stoppedPhaseExhausted
  | stoppedTPairExhausted
structure BK05WordRawLeaf where
  status : BK05WordLeafStatus
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator QubitSpace
def importRawStatus : BK05RawLeafKind → BK05WordLeafStatus
  | .targetHit => .live
  | .phaseExhausted => .stoppedPhaseExhausted
  | .tPairExhausted => .stoppedTPairExhausted
def importRawLeaf (leaf : BK05RawLeaf) : BK05WordRawLeaf :=
  .mk (importRawStatus leaf.kind) leaf.history leaf.ledger leaf.raw
def importRawLeaves (leaves : List BK05RawLeaf) : List BK05WordRawLeaf :=
  leaves.map importRawLeaf
def wordRawWeight (leaf : BK05WordRawLeaf) : Real :=
  (LinearMap.trace Complex QubitSpace leaf.raw).re
def wordRawMass (leaves : List BK05WordRawLeaf) : Real :=
  (leaves.map wordRawWeight).sum
def wordRawAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  (leaves.map BK05WordRawLeaf.raw).sum
def stoppingStep
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf)
    (leaf : BK05WordRawLeaf) : List BK05WordRawLeaf :=
  match leaf.status with
  | .live => continuation leaf.history leaf.ledger leaf.raw
  | .stoppedPhaseExhausted => [leaf]
  | .stoppedTPairExhausted => [leaf]
def stoppingBind (leaves : List BK05WordRawLeaf)
    (continuation : List Bool → ResourceLedger BK05ResourceToken →
      Operator QubitSpace → List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  leaves.flatMap (stoppingStep continuation)
def hPhaseTarget : BK05WordPolarity → ZMod 8
  | .normal => (1 : ZMod 8)
  | .inverse => -1
def tPhaseTarget : BK05WordPolarity → ZMod 12
  | .normal => (1 : ZMod 12)
  | .inverse => -1
def runHPhaseFrom
    (h : DensityOperator QubitSpace) (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05WordRawLeaf :=
  importRawLeaves (hRetry h (hPhaseTarget sign) (8 * blocks) 0 ledger history data)
def runTPhaseFrom
    (t : DensityOperator QubitSpace) (pairAttempts : Nat)
    (sign : BK05WordPolarity) (blocks : Nat)
    (ledger : ResourceLedger BK05ResourceToken) (history : List Bool)
    (data : Operator QubitSpace) : List BK05WordRawLeaf :=
  importRawLeaves
    (tRetry t pairAttempts (tPhaseTarget sign) (12 * blocks) 0 ledger history data)
def signedHLetter (theta : Real) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive .h
  | .inverse => .negative .h
def signedKLetter (theta : Real) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive .k
  | .inverse => .negative .k
noncomputable def signedHTransport :
    BK05WordPolarity → UnitaryTransport QubitSpace QubitSpace
  | .normal => hadamardTransport
  | .inverse => hadamardTransport
noncomputable def signedKTransport :
    BK05WordPolarity → UnitaryTransport QubitSpace QubitSpace
  | .normal => phaseTransport
  | .inverse => phaseTransport.symm
noncomputable def signedHRawLinear :
    BK05WordPolarity → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .normal => hadamardTransport.conjOperatorLinearMap
  | .inverse => hadamardTransport.conjOperatorLinearMap
noncomputable def signedKRawLinear :
    BK05WordPolarity → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .normal => phaseTransport.conjOperatorLinearMap
  | .inverse => phaseTransport.symm.conjOperatorLinearMap
theorem signedHRawLinear_trace
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (signedHRawLinear sign raw) =
      LinearMap.trace Complex QubitSpace raw := by
  cases sign <;> simpa [signedHRawLinear] using
    hadamardTransport.trace_conjOperator raw
theorem signedKRawLinear_trace
    (sign : BK05WordPolarity) (raw : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (signedKRawLinear sign raw) =
      LinearMap.trace Complex QubitSpace raw := by
  cases sign with
  | normal =>
      simpa [signedKRawLinear] using phaseTransport.trace_conjOperator raw
  | inverse =>
      simpa [signedKRawLinear] using phaseTransport.symm.trace_conjOperator raw
noncomputable def deterministicLiveLeaf
    (U : UnitaryTransport QubitSpace QubitSpace)
    (history : List Bool) (ledger : ResourceLedger BK05ResourceToken)
    (raw : Operator QubitSpace) : BK05WordRawLeaf :=
  ⟨.live, history, ledger, U.conjOperator raw⟩
noncomputable def deterministicContinuation
    (U : UnitaryTransport QubitSpace QubitSpace) :
    List Bool → ResourceLedger BK05ResourceToken → Operator QubitSpace →
      List BK05WordRawLeaf :=
  fun history ledger raw => [deterministicLiveLeaf U history ledger raw]
noncomputable def runDeterministic
    (U : UnitaryTransport QubitSpace QubitSpace)
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  stoppingBind leaves (deterministicContinuation U)
noncomputable def oneShotSignedAngle (theta : Real) (coin : Bool) : Real :=
  if coin then theta else -theta
noncomputable def hIdealHistoryRaw : List Bool →
    Operator QubitSpace → Operator QubitSpace
  | [], data => data
  | coin :: coins, data =>
      hIdealHistoryRaw coins (hStepRaw hMagicState coin data)
def rawAggregateOfKind (kind : BK05RawLeafKind)
    (leaves : List BK05RawLeaf) : Operator QubitSpace :=
  let retained := leaves.filter fun leaf => leaf.kind == kind
  rawAggregate retained
def hTargetHitCoeff (target : ZMod 8) : Nat → ZMod 8 → Real
  | 0, position => if position = target then 1 else 0
  | remaining + 1, position =>
      if position = target then 1 else
        (hTargetHitCoeff target remaining (position + 1) +
          hTargetHitCoeff target remaining (position - 1)) / 2
noncomputable def phaseCycleTargetChannel
    (q : Nat) (target : ZMod q) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  (OneQubitMagic.phaseShiftTransport
    (phaseCycleAngle q * target.val)).conjOperatorLinearMap
def hTargetHitHistoryWeight (leaves : List BK05RawLeaf) : Complex :=
  (leaves.filter fun leaf => leaf.kind == .targetHit).map
    (fun leaf => (1 / 2 : Complex) ^ leaf.history.length) |>.sum
theorem phaseCycleTargetChannel_trace
    (q : Nat) (target : ZMod q) (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
        (phaseCycleTargetChannel q target data) =
      LinearMap.trace Complex QubitSpace data := by
  simpa [phaseCycleTargetChannel] using
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle q * target.val)).trace_conjOperator data
noncomputable def hRetryTargetHitLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then LinearMap.id else 0
  | remaining + 1, position =>
      if position = target then LinearMap.id else
        (hRetryTargetHitLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryTargetHitLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)
noncomputable def hRetryPhaseExhaustedLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then 0 else LinearMap.id
  | remaining + 1, position =>
      if position = target then 0 else
        (hRetryPhaseExhaustedLinear h target remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryPhaseExhaustedLinear h target remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)
noncomputable def hRetryStoppingTotalLinear
    (h : DensityOperator QubitSpace) (target : ZMod 8)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Nat → ZMod 8 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, position => if position = target then success else LinearMap.id
  | remaining + 1, position =>
      if position = target then success else
        (hRetryStoppingTotalLinear h target success remaining (position + 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) true) +
        (hRetryStoppingTotalLinear h target success remaining (position - 1)).comp
            (phaseBranchRawLinear (hPhaseRaw h) false)
noncomputable def runHSignedLetter
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) (leaves : List BK05WordRawLeaf) :
    List BK05WordRawLeaf :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 4)) :=
    match atom with
    | .h => runDeterministic (signedHTransport sign) leaves
    | .k => runDeterministic (signedKTransport sign) leaves
    | .phase => stoppingBind leaves
        (fun history ledger raw => runHPhaseFrom h sign blocks ledger history raw)
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom
noncomputable def runHPhysicalLetters
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → List BK05WordRawLeaf → List BK05WordRawLeaf
  | [], leaves => leaves
  | letter :: tail, leaves =>
      runHPhysicalLetters h blocks tail (runHSignedLetter h blocks letter leaves)
noncomputable def runHSignedWord
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  runHPhysicalLetters h blocks letters.reverse leaves
def wordRawStatusMatches (expected actual : BK05WordLeafStatus) : Bool :=
  match expected, actual with
  | .live, .live => true
  | .stoppedPhaseExhausted, .stoppedPhaseExhausted => true
  | .stoppedTPairExhausted, .stoppedTPairExhausted => true
  | _, _ => false
def wordRawAggregateOfStatus (status : BK05WordLeafStatus)
    : List BK05WordRawLeaf → Operator QubitSpace
  | [] => 0
  | leaf :: leaves =>
      if wordRawStatusMatches status leaf.status then
        leaf.raw + wordRawAggregateOfStatus status leaves
      else wordRawAggregateOfStatus status leaves
def wordRawLiveAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  wordRawAggregateOfStatus .live leaves
def wordRawStoppedAggregate (leaves : List BK05WordRawLeaf) :
    Operator QubitSpace :=
  wordRawAggregateOfStatus .stoppedPhaseExhausted leaves +
    wordRawAggregateOfStatus .stoppedTPairExhausted leaves
noncomputable def hSignedLetterTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 4)) :=
    match atom with
    | .h => success.comp (signedHRawLinear sign)
    | .k => success.comp (signedKRawLinear sign)
    | .phase => hRetryStoppingTotalLinear h (hPhaseTarget sign) success (8 * blocks) 0
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom
noncomputable def hPhysicalLettersTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      hSignedLetterTotalLinear h blocks letter
        (hPhysicalLettersTotalLinear h blocks tail success)
noncomputable def hSignedWordTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  hPhysicalLettersTotalLinear h blocks letters.reverse success
noncomputable def hWordLiveLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail =>
      let tailLive := hWordLiveLinear h blocks tail
      match letter with
      | .positive .h => (signedHRawLinear .normal).comp tailLive
      | .positive .k => (signedKRawLinear .normal).comp tailLive
      | .positive .phase =>
          (hRetryTargetHitLinear h (hPhaseTarget .normal) (8 * blocks) 0).comp tailLive
      | .negative .h => (signedHRawLinear .inverse).comp tailLive
      | .negative .k => (signedKRawLinear .inverse).comp tailLive
      | .negative .phase =>
          (hRetryTargetHitLinear h (hPhaseTarget .inverse) (8 * blocks) 0).comp tailLive
noncomputable def hWordPhaseStoppedLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := hWordLiveLinear h blocks tail
      match letter with
      | .positive .h => hWordPhaseStoppedLinear h blocks tail
      | .positive .k => hWordPhaseStoppedLinear h blocks tail
      | .positive .phase =>
          (hRetryPhaseExhaustedLinear h (hPhaseTarget .normal) (8 * blocks) 0).comp
            tailLive + hWordPhaseStoppedLinear h blocks tail
      | .negative .h => hWordPhaseStoppedLinear h blocks tail
      | .negative .k => hWordPhaseStoppedLinear h blocks tail
      | .negative .phase =>
          (hRetryPhaseExhaustedLinear h (hPhaseTarget .inverse) (8 * blocks) 0).comp
            tailLive + hWordPhaseStoppedLinear h blocks tail
noncomputable def hFixedIdealLetterStateLinear :
    BK05SignedPhaseLetter (-Real.pi / 4) → Operator QubitSpace
  | .positive .h => (signedHTransport .normal).toLinearEquiv.toLinearMap
  | .positive .k => (signedKTransport .normal).toLinearEquiv.toLinearMap
  | .positive .phase => phaseCycleTargetAction 8 (hPhaseTarget .normal)
  | .negative .h => (signedHTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .k => (signedKTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .phase => phaseCycleTargetAction 8 (hPhaseTarget .inverse)
noncomputable def hFixedIdealLetterLinear :
    BK05SignedPhaseLetter (-Real.pi / 4) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .positive .h => signedHRawLinear .normal
  | .positive .k => signedKRawLinear .normal
  | .positive .phase => phaseCycleTargetChannel 8 (hPhaseTarget .normal)
  | .negative .h => signedHRawLinear .inverse
  | .negative .k => signedKRawLinear .inverse
  | .negative .phase => phaseCycleTargetChannel 8 (hPhaseTarget .inverse)
noncomputable def hFixedIdealWordLinear :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail => (hFixedIdealLetterLinear letter).comp (hFixedIdealWordLinear tail)
theorem hFixedIdealLetterLinear_trace
    (letter : BK05SignedPhaseLetter (-Real.pi / 4))
    (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (hFixedIdealLetterLinear letter data) =
      LinearMap.trace Complex QubitSpace data := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => simpa [hFixedIdealLetterLinear] using signedHRawLinear_trace .normal data
      | k => simpa [hFixedIdealLetterLinear] using signedKRawLinear_trace .normal data
      | phase =>
          simpa [hFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 8 (hPhaseTarget .normal) data
  | negative atom =>
      cases atom with
      | h => simpa [hFixedIdealLetterLinear] using signedHRawLinear_trace .inverse data
      | k => simpa [hFixedIdealLetterLinear] using signedKRawLinear_trace .inverse data
      | phase =>
          simpa [hFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 8 (hPhaseTarget .inverse) data
theorem hFixedIdealWordLinear_trace :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
      (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace (hFixedIdealWordLinear letters data) =
        LinearMap.trace Complex QubitSpace data := by
  intro letters
  induction letters with
  | nil =>
      intro data
      rfl
  | cons letter tail ih =>
      intro data
      simpa [hFixedIdealWordLinear, LinearMap.comp_apply] using
        (hFixedIdealLetterLinear_trace letter
          (hFixedIdealWordLinear tail data)).trans (ih data)
noncomputable def hWordLiveCoeff (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → Complex
  | [] => 1
  | .positive .h :: tail => hWordLiveCoeff blocks tail
  | .positive .k :: tail => hWordLiveCoeff blocks tail
  | .positive .phase :: tail =>
      (hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 : Complex) *
        hWordLiveCoeff blocks tail
  | .negative .h :: tail => hWordLiveCoeff blocks tail
  | .negative .k :: tail => hWordLiveCoeff blocks tail
  | .negative .phase :: tail =>
      (hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 : Complex) *
        hWordLiveCoeff blocks tail
def hWordLiveProbability (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) → Real
  | [] => 1
  | .positive .h :: tail => hWordLiveProbability blocks tail
  | .positive .k :: tail => hWordLiveProbability blocks tail
  | .positive .phase :: tail =>
      hTargetHitCoeff (hPhaseTarget .normal) (8 * blocks) 0 *
        hWordLiveProbability blocks tail
  | .negative .h :: tail => hWordLiveProbability blocks tail
  | .negative .k :: tail => hWordLiveProbability blocks tail
  | .negative .phase :: tail =>
      hTargetHitCoeff (hPhaseTarget .inverse) (8 * blocks) 0 *
        hWordLiveProbability blocks tail
noncomputable def hWordStoppingTotalLinear
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      match letter with
      | .positive .h =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedHRawLinear .normal))
      | .positive .k =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedKRawLinear .normal))
      | .positive .phase =>
          hWordStoppingTotalLinear h blocks tail
            (hRetryStoppingTotalLinear h (hPhaseTarget .normal) success (8 * blocks) 0)
      | .negative .h =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedHRawLinear .inverse))
      | .negative .k =>
          hWordStoppingTotalLinear h blocks tail
            (success.comp (signedKRawLinear .inverse))
      | .negative .phase =>
          hWordStoppingTotalLinear h blocks tail
            (hRetryStoppingTotalLinear h (hPhaseTarget .inverse) success (8 * blocks) 0)
noncomputable def runTSignedLetter
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) (leaves : List BK05WordRawLeaf) :
    List BK05WordRawLeaf :=
  let execute (sign : BK05WordPolarity) (atom : BK05PhaseAtom (-Real.pi / 6)) :=
    match atom with
    | .h => runDeterministic (signedHTransport sign) leaves
    | .k => runDeterministic (signedKTransport sign) leaves
    | .phase => stoppingBind leaves
        (fun history ledger raw => runTPhaseFrom t pairAttempts sign blocks ledger history raw)
  match letter with
  | .positive atom => execute .normal atom
  | .negative atom => execute .inverse atom
noncomputable def runTPhysicalLetters
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → List BK05WordRawLeaf → List BK05WordRawLeaf
  | [], leaves => leaves
  | letter :: tail, leaves =>
      runTPhysicalLetters t pairAttempts blocks tail
        (runTSignedLetter t pairAttempts blocks letter leaves)
noncomputable def runTSignedWord
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
    (leaves : List BK05WordRawLeaf) : List BK05WordRawLeaf :=
  runTPhysicalLetters t pairAttempts blocks letters.reverse leaves
noncomputable def tSupplyStoppingComponentLinear
    (t : DensityOperator QubitSpace) : Nat →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | 0, _, _, onPairExhausted => onPairExhausted
  | attempts + 1, nextTrue, nextFalse, onPairExhausted =>
      nextTrue.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) true) +
        nextFalse.comp (phaseBranchRawLinear (tAcceptedPhaseRaw t) false) +
        (tSupplyStoppingComponentLinear t attempts
          nextTrue nextFalse onPairExhausted).comp (tRejectedDataRawLinear t)
def tSupplyStoppingComponentValue
    (nextTrue nextFalse onPairExhausted : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    List BK05TSupplyOutcome → Operator QubitSpace
  | [] => 0
  | .accepted _ _ data phaseToken :: outcomes =>
      nextTrue (phaseBranchRaw phaseToken data true) +
        nextFalse (phaseBranchRaw phaseToken data false) +
        tSupplyStoppingComponentValue nextTrue nextFalse onPairExhausted outcomes
  | .exhausted _ _ data :: outcomes =>
      onPairExhausted data +
        tSupplyStoppingComponentValue nextTrue nextFalse onPairExhausted outcomes
noncomputable def tSupplyTargetHitLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
noncomputable def tSupplyPhaseExhaustedLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
noncomputable def tSupplyPairExhaustedLinear
    (t : DensityOperator QubitSpace) (attempts : Nat)
    (nextTrue nextFalse : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tSupplyStoppingComponentLinear t attempts nextTrue nextFalse LinearMap.id
noncomputable def tRetryTargetHitLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then LinearMap.id else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            tSupplyTargetHitLinear t pairAttempts
              (tRetryTargetHitLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryTargetHitLinear t pairAttempts target nextRemaining (position - 1))
noncomputable def tRetryPhaseExhaustedLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then 0 else
        match remaining with
        | 0 => LinearMap.id
        | nextRemaining + 1 =>
            tSupplyPhaseExhaustedLinear t pairAttempts
              (tRetryPhaseExhaustedLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryPhaseExhaustedLinear t pairAttempts target nextRemaining (position - 1))
noncomputable def tRetryPairExhaustedLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then 0 else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            tSupplyPairExhaustedLinear t pairAttempts
              (tRetryPairExhaustedLinear t pairAttempts target nextRemaining (position + 1))
              (tRetryPairExhaustedLinear t pairAttempts target nextRemaining (position - 1))
noncomputable def tWordLiveLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => (signedHRawLinear .normal).comp tailLive
      | .positive .k => (signedKRawLinear .normal).comp tailLive
      | .positive .phase =>
          (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive
      | .negative .h => (signedHRawLinear .inverse).comp tailLive
      | .negative .k => (signedKRawLinear .inverse).comp tailLive
      | .negative .phase =>
          (tRetryTargetHitLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive
noncomputable def tWordPhaseStoppedLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .positive .k => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .positive .phase =>
          (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive + tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .h => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .k => tWordPhaseStoppedLinear t pairAttempts blocks tail
      | .negative .phase =>
          (tRetryPhaseExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive + tWordPhaseStoppedLinear t pairAttempts blocks tail
noncomputable def tWordPairStoppedLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => 0
  | letter :: tail =>
      let tailLive := tWordLiveLinear t pairAttempts blocks tail
      match letter with
      | .positive .h => tWordPairStoppedLinear t pairAttempts blocks tail
      | .positive .k => tWordPairStoppedLinear t pairAttempts blocks tail
      | .positive .phase =>
          (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .normal) (12 * blocks) 0).comp
            tailLive + tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .h => tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .k => tWordPairStoppedLinear t pairAttempts blocks tail
      | .negative .phase =>
          (tRetryPairExhaustedLinear t pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0).comp
            tailLive + tWordPairStoppedLinear t pairAttempts blocks tail
noncomputable def tWordTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace :=
  tWordLiveLinear t pairAttempts blocks letters +
    tWordPhaseStoppedLinear t pairAttempts blocks letters +
    tWordPairStoppedLinear t pairAttempts blocks letters
def tTargetHitCoeff (pairAttempts : Nat) (target : ZMod 12) :
    Nat → ZMod 12 → Real
  | remaining, position =>
      if position = target then 1 else
        match remaining with
        | 0 => 0
        | nextRemaining + 1 =>
            ((1 - (1 / 3 : Real) ^ pairAttempts) / 2) *
              (tTargetHitCoeff pairAttempts target nextRemaining (position + 1) +
                tTargetHitCoeff pairAttempts target nextRemaining (position - 1))
noncomputable def tFixedIdealLetterStateLinear :
    BK05SignedPhaseLetter (-Real.pi / 6) → Operator QubitSpace
  | .positive .h => (signedHTransport .normal).toLinearEquiv.toLinearMap
  | .positive .k => (signedKTransport .normal).toLinearEquiv.toLinearMap
  | .positive .phase => phaseCycleTargetAction 12 (tPhaseTarget .normal)
  | .negative .h => (signedHTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .k => (signedKTransport .inverse).toLinearEquiv.toLinearMap
  | .negative .phase => phaseCycleTargetAction 12 (tPhaseTarget .inverse)
noncomputable def tFixedIdealLetterLinear :
    BK05SignedPhaseLetter (-Real.pi / 6) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | .positive .h => signedHRawLinear .normal
  | .positive .k => signedKRawLinear .normal
  | .positive .phase => phaseCycleTargetChannel 12 (tPhaseTarget .normal)
  | .negative .h => signedHRawLinear .inverse
  | .negative .k => signedKRawLinear .inverse
  | .negative .phase => phaseCycleTargetChannel 12 (tPhaseTarget .inverse)
noncomputable def tFixedIdealWordLinear :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [] => LinearMap.id
  | letter :: tail => (tFixedIdealLetterLinear letter).comp (tFixedIdealWordLinear tail)
theorem tFixedIdealLetterLinear_trace
    (letter : BK05SignedPhaseLetter (-Real.pi / 6))
    (data : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace (tFixedIdealLetterLinear letter data) =
      LinearMap.trace Complex QubitSpace data := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => simpa [tFixedIdealLetterLinear] using signedHRawLinear_trace .normal data
      | k => simpa [tFixedIdealLetterLinear] using signedKRawLinear_trace .normal data
      | phase =>
          simpa [tFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 12 (tPhaseTarget .normal) data
  | negative atom =>
      cases atom with
      | h => simpa [tFixedIdealLetterLinear] using signedHRawLinear_trace .inverse data
      | k => simpa [tFixedIdealLetterLinear] using signedKRawLinear_trace .inverse data
      | phase =>
          simpa [tFixedIdealLetterLinear] using
            phaseCycleTargetChannel_trace 12 (tPhaseTarget .inverse) data
theorem tFixedIdealWordLinear_trace :
    ∀ (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
      (data : Operator QubitSpace),
      LinearMap.trace Complex QubitSpace (tFixedIdealWordLinear letters data) =
        LinearMap.trace Complex QubitSpace data := by
  intro letters
  induction letters with
  | nil =>
      intro data
      rfl
  | cons letter tail ih =>
      intro data
      simpa [tFixedIdealWordLinear, LinearMap.comp_apply] using
        (tFixedIdealLetterLinear_trace letter
          (tFixedIdealWordLinear tail data)).trans (ih data)
noncomputable def tWordLiveCoeff (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → Complex
  | [] => 1
  | .positive .h :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .positive .k :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .positive .phase :: tail =>
      (tTargetHitCoeff pairAttempts (tPhaseTarget .normal) (12 * blocks) 0 : Complex) *
        tWordLiveCoeff pairAttempts blocks tail
  | .negative .h :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .negative .k :: tail => tWordLiveCoeff pairAttempts blocks tail
  | .negative .phase :: tail =>
      (tTargetHitCoeff pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0 : Complex) *
        tWordLiveCoeff pairAttempts blocks tail
def tWordLiveProbability (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) → Real
  | [] => 1
  | .positive .h :: tail => tWordLiveProbability pairAttempts blocks tail
  | .positive .k :: tail => tWordLiveProbability pairAttempts blocks tail
  | .positive .phase :: tail =>
      tTargetHitCoeff pairAttempts (tPhaseTarget .normal) (12 * blocks) 0 *
        tWordLiveProbability pairAttempts blocks tail
  | .negative .h :: tail => tWordLiveProbability pairAttempts blocks tail
  | .negative .k :: tail => tWordLiveProbability pairAttempts blocks tail
  | .negative .phase :: tail =>
      tTargetHitCoeff pairAttempts (tPhaseTarget .inverse) (12 * blocks) 0 *
        tWordLiveProbability pairAttempts blocks tail
noncomputable def tRetryStoppingTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12)
    (success : Operator QubitSpace →ₗ[Complex] Operator QubitSpace) :
    Nat → ZMod 12 → Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | remaining, position =>
      if position = target then success else
        match remaining with
        | 0 => LinearMap.id
        | nextRemaining + 1 =>
            tSupplyAggregateLinear t pairAttempts
              (tRetryStoppingTotalLinear t pairAttempts target success
                nextRemaining (position + 1))
              (tRetryStoppingTotalLinear t pairAttempts target success
                nextRemaining (position - 1))
noncomputable def tWordStoppingTotalLinear
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      (Operator QubitSpace →ₗ[Complex] Operator QubitSpace) →
        Operator QubitSpace →ₗ[Complex] Operator QubitSpace
  | [], success => success
  | letter :: tail, success =>
      match letter with
      | .positive .h =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedHRawLinear .normal))
      | .positive .k =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedKRawLinear .normal))
      | .positive .phase =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .normal) success
              (12 * blocks) 0)
      | .negative .h =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedHRawLinear .inverse))
      | .negative .k =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (success.comp (signedKRawLinear .inverse))
      | .negative .phase =>
          tWordStoppingTotalLinear t pairAttempts blocks tail
            (tRetryStoppingTotalLinear t pairAttempts (tPhaseTarget .inverse) success
              (12 * blocks) 0)
noncomputable def selectedWireFactorization
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire) :
    UnitaryTransport (QubitRegister Wire)
      (CompositeSystem QubitSpace (QubitRegister (OtherWires wire))) := by
  let sourceBasis := EuclideanSpace.basisFun (Bitstring Wire) Complex
  let selectedBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let restBasis := EuclideanSpace.basisFun
    (Bitstring (OtherWires wire)) Complex
  let targetBasis := selectedBasis.tensorProduct restBasis
  let U := sourceBasis.equiv targetBasis (singleQubitIndexEquiv wire)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
noncomputable def krausSeq
    {ι κ H K L : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily ι H K) (D : FiniteKrausFamily κ K L) :
    FiniteKrausFamily (ι × κ) H L where
  operator index := (D.operator index.2).comp (E.operator index.1)
theorem krausSeq_inducedMap_apply
    {ι κ H K L : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily ι H K) (D : FiniteKrausFamily κ K L)
    (A : Operator H) :
    (krausSeq E D).inducedMap A = D.inducedMap (E.inducedMap A) := by
  classical
  apply LinearMap.ext
  intro x
  simp only [FiniteKrausFamily.inducedMap_apply, krausSeq,
    LinearMap.adjoint_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum]
noncomputable def tensorIdKraus
    {κ H : Type} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (E : FiniteKrausFamily κ H H)
    (R : Type) [NormedAddCommGroup R] [InnerProductSpace Complex R]
    [FiniteQuantumSystem R] :
    FiniteKrausFamily κ (CompositeSystem H R) (CompositeSystem H R) where
  operator i := TensorProduct.map (E.operator i) (1 : Operator R)
noncomputable def selectedWireKraus
    {κ : Type} [Fintype κ] {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (E : FiniteKrausFamily κ QubitSpace QubitSpace) :
    FiniteKrausFamily κ (QubitRegister Wire) (QubitRegister Wire) :=
  (tensorIdKraus E (QubitRegister (OtherWires wire))).unitaryTransport
    (selectedWireFactorization wire).symm
    (selectedWireFactorization wire).symm
@[simp]
theorem splitAtWire_mergeAtWire_private
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] (wire : Wire)
    (bits : Fin 2 × Bitstring (OtherWires wire)) :
    splitAtWire wire (mergeAtWire wire bits) = bits :=
  (singleQubitIndexEquiv wire).apply_symm_apply bits
noncomputable def unitaryGateKraus (gate : UnitaryGate (Fin 2)) :
    FiniteKrausFamily Unit QubitSpace QubitSpace where
  operator _ := Matrix.toEuclideanLin
    (gate : Matrix (Fin 2) (Fin 2) Complex)
noncomputable def hFixedIdealLetterTransport :
    BK05SignedPhaseLetter (-Real.pi / 4) →
      UnitaryTransport QubitSpace QubitSpace
  | .positive .h => signedHTransport .normal
  | .positive .k => signedKTransport .normal
  | .positive .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 8 * (hPhaseTarget .normal).val)
  | .negative .h => signedHTransport .inverse
  | .negative .k => signedKTransport .inverse
  | .negative .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 8 * (hPhaseTarget .inverse).val)
noncomputable def tFixedIdealLetterTransport :
    BK05SignedPhaseLetter (-Real.pi / 6) →
      UnitaryTransport QubitSpace QubitSpace
  | .positive .h => signedHTransport .normal
  | .positive .k => signedKTransport .normal
  | .positive .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 12 * (tPhaseTarget .normal).val)
  | .negative .h => signedHTransport .inverse
  | .negative .k => signedKTransport .inverse
  | .negative .phase =>
      OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle 12 * (tPhaseTarget .inverse).val)
noncomputable def hFixedIdealWordTransport :
    List (BK05SignedPhaseLetter (-Real.pi / 4)) →
      UnitaryTransport QubitSpace QubitSpace
  | [] => UnitaryTransport.identity QubitSpace
  | letter :: tail =>
      (hFixedIdealWordTransport tail).trans (hFixedIdealLetterTransport letter)
noncomputable def tFixedIdealWordTransport :
    List (BK05SignedPhaseLetter (-Real.pi / 6)) →
      UnitaryTransport QubitSpace QubitSpace
  | [] => UnitaryTransport.identity QubitSpace
  | letter :: tail =>
      (tFixedIdealWordTransport tail).trans (tFixedIdealLetterTransport letter)
noncomputable def channelKrausSize
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) : Nat :=
  Classical.choose Phi.exists_finiteKrausFamily_representation
noncomputable def channelKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) :
    FiniteKrausFamily (Fin (channelKrausSize Phi)) H K :=
  Classical.choose
    (Classical.choose_spec Phi.exists_finiteKrausFamily_representation)
theorem channelKraus_inducedMap_eq
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) :
    (channelKraus Phi).inducedMap = Phi.toLinearMap :=
  (Classical.choose_spec
    (Classical.choose_spec Phi.exists_finiteKrausFamily_representation)).2
theorem channelKraus_inducedMap_apply
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : QuantumChannel H K) (A : Operator H) :
    (channelKraus Phi).inducedMap A = Phi A := by
  exact LinearMap.congr_fun (channelKraus_inducedMap_eq Phi) A
theorem prepareRightKraus_inducedMap_apply
    {H K : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    (ThermalEncoding.prepareRightKraus H K sigma).inducedMap A =
      TensorProduct.map A sigma.toOperator := by
  simpa [ThermalEncoding.prepareRight] using
    ThermalEncoding.prepareRight_apply H K sigma A
noncomputable def idTensorKraus
    {kappa K L : Type} [Fintype kappa]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily kappa K L)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] :
    FiniteKrausFamily kappa (CompositeSystem H K) (CompositeSystem H L) where
  operator i := TensorProduct.map (1 : Operator H) (E.operator i)
theorem tensorMap_sum_right_kraus
    {kappa H K : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (A : Operator H) (B : kappa -> Operator K) :
    TensorProduct.map A (∑ i, B i) =
      ∑ i, TensorProduct.map A (B i) := by
  classical
  induction (Finset.univ : Finset kappa) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, TensorProduct.map_add_right, ih]
theorem idTensorKraus_inducedMap_tensor
    {kappa H K L : Type} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (E : FiniteKrausFamily kappa K L) (A : Operator H) (B : Operator K) :
    (idTensorKraus E H).inducedMap (TensorProduct.map A B) =
      TensorProduct.map A (E.inducedMap B) := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply, tensorMap_sum_right_kraus]
  apply Finset.sum_congr rfl
  intro i _
  simp only [idTensorKraus]
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  simp only [<- TensorProduct.map_comp]
  congr 1
noncomputable def phaseBranchKraus (coin : Bool) :
    FiniteKrausFamily Unit TwoQubit.TwoQubitSpace TwoQubit.TwoQubitSpace where
  operator _ := jointStabilizerProjector zzMeasurement.checks
    zzMeasurement.commute (observedRetrySyndrome coin)
theorem phaseBranchKraus_inducedMap_apply (coin : Bool)
    (A : Operator TwoQubit.TwoQubitSpace) :
    (phaseBranchKraus coin).inducedMap A = observedBranchLinear coin A := by
  rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_unique,
    observedBranchLinear_apply]
  change _ = (jointStabilizerInstrument zzMeasurement.checks
    zzMeasurement.commute).branchOperator (observedRetrySyndrome coin) A
  rw [jointStabilizerInstrument_branchOperator]
  simp only [phaseBranchKraus, jointStabilizerProjector_adjoint]
  rfl
noncomputable def hPhaseDensity (h : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (QuantumChannel.unitaryConj hResourceTransport).mapDensity h
noncomputable def hStepKraus (h : DensityOperator QubitSpace)
    (coin : Bool) :=
  krausSeq (ThermalEncoding.prepareRightKraus
      QubitSpace QubitSpace (hPhaseDensity h))
    (krausSeq
      (channelKraus (QuantumChannel.unitaryConj
        TwoQubit.tensorRegisterTransport))
      (krausSeq (phaseBranchKraus coin) (channelKraus oneShotPostprocess)))
theorem hStepKraus_inducedMap_apply
    (h : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) :
    (hStepKraus h coin).inducedMap data = hStepRaw h coin data := by
  rw [hStepKraus, krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    channelKraus_inducedMap_apply, channelKraus_inducedMap_apply,
    phaseBranchKraus_inducedMap_apply]
  rfl
theorem hStepLinear_completelyPositive
    (h : DensityOperator QubitSpace) (coin : Bool) :
    CompletelyPositive (phaseBranchRawLinear (hPhaseRaw h) coin) := by
  rw [show phaseBranchRawLinear (hPhaseRaw h) coin =
      (hStepKraus h coin).inducedMap by
    apply LinearMap.ext
    intro data
    rw [hStepKraus_inducedMap_apply]
    rfl]
  exact (hStepKraus h coin).inducedMap_completelyPositive
noncomputable def tPairDensity (t : DensityOperator QubitSpace) :
    DensityOperator TwoQubit.TwoQubitSpace :=
  (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport).mapDensity
    (DensityOperator.tensorDensity t t)
noncomputable def tAcceptedStepKraus
    (t : DensityOperator QubitSpace) (coin : Bool) :=
  krausSeq
    (ThermalEncoding.prepareRightKraus
      QubitSpace TwoQubit.TwoQubitSpace (tPairDensity t))
    (krausSeq
      (idTensorKraus (phaseBranchKraus true) QubitSpace)
      (krausSeq
        (idTensorKraus (channelKraus oneShotPostprocess) QubitSpace)
        (krausSeq
          (idTensorKraus
            (channelKraus (QuantumChannel.unitaryConj hadamardTransport))
            QubitSpace)
          (krausSeq
            (channelKraus (QuantumChannel.unitaryConj
              TwoQubit.tensorRegisterTransport))
            (krausSeq (phaseBranchKraus coin)
              (channelKraus oneShotPostprocess))))))
set_option maxRecDepth 4000 in
theorem tAcceptedStepKraus_inducedMap_apply
    (t : DensityOperator QubitSpace) (coin : Bool)
    (data : Operator QubitSpace) :
    (tAcceptedStepKraus t coin).inducedMap data =
      phaseBranchRaw (tAcceptedPhaseRaw t) data coin := by
  rw [tAcceptedStepKraus, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, phaseBranchKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, channelKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, channelKraus_inducedMap_apply,
    channelKraus_inducedMap_apply, phaseBranchKraus_inducedMap_apply,
    channelKraus_inducedMap_apply]
  rfl
theorem tAcceptedStepLinear_completelyPositive
    (t : DensityOperator QubitSpace) (coin : Bool) :
    CompletelyPositive (phaseBranchRawLinear (tAcceptedPhaseRaw t) coin) := by
  rw [show phaseBranchRawLinear (tAcceptedPhaseRaw t) coin =
      (tAcceptedStepKraus t coin).inducedMap by
    apply LinearMap.ext
    intro data
    exact (tAcceptedStepKraus_inducedMap_apply t coin data).symm]
  exact (tAcceptedStepKraus t coin).inducedMap_completelyPositive
noncomputable def tRejectStepKraus (t : DensityOperator QubitSpace) :=
  krausSeq
    (ThermalEncoding.prepareRightKraus
      QubitSpace TwoQubit.TwoQubitSpace (tPairDensity t))
    (krausSeq
      (idTensorKraus (phaseBranchKraus false) QubitSpace)
      (channelKraus
        (partialTraceRightRaw_cptp QubitSpace TwoQubit.TwoQubitSpace)))
theorem tRejectStepKraus_inducedMap_apply
    (t : DensityOperator QubitSpace) (data : Operator QubitSpace) :
    (tRejectStepKraus t).inducedMap data = tRejectedDataRaw data t := by
  rw [tRejectStepKraus, krausSeq_inducedMap_apply,
    krausSeq_inducedMap_apply, prepareRightKraus_inducedMap_apply,
    idTensorKraus_inducedMap_tensor, phaseBranchKraus_inducedMap_apply,
    channelKraus_inducedMap_apply]
  rfl
theorem tRejectStepLinear_completelyPositive
    (t : DensityOperator QubitSpace) :
    CompletelyPositive (tRejectedDataRawLinear t) := by
  rw [show tRejectedDataRawLinear t = (tRejectStepKraus t).inducedMap by
    apply LinearMap.ext
    intro data
    exact (tRejectStepKraus_inducedMap_apply t data).symm]
  exact (tRejectStepKraus t).inducedMap_completelyPositive
theorem completelyPositive_zero_local
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    CompletelyPositive
      (0 : Operator H →ₗ[Complex] Operator K) := by
  intro n M hM
  constructor
  · intro i j
    simp [OperatorMatrix.map]
  · intro x
    simp [OperatorMatrix.map]
theorem completelyPositive_id_local
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] :
    CompletelyPositive
      (LinearMap.id : Operator H →ₗ[Complex] Operator H) :=
  (QuantumChannel.id H).completely_positive
theorem completelyPositive_add_local
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {Phi Psi : Operator H →ₗ[Complex] Operator K}
    (hPhi : CompletelyPositive Phi) (hPsi : CompletelyPositive Psi) :
    CompletelyPositive (Phi + Psi) := by
  intro n M hM
  constructor
  · intro i j
    simp only [OperatorMatrix.map, LinearMap.add_apply, map_add]
    exact congrArg₂ (fun A B => A + B)
      ((hPhi n M hM).1 i j) ((hPsi n M hM).1 i j)
  · intro x
    have hp := (hPhi n M hM).2 x
    have hq := (hPsi n M hM).2 x
    simpa only [OperatorMatrix.map, LinearMap.add_apply, inner_add_left,
      Complex.add_re, Finset.sum_add_distrib] using add_nonneg hp hq
theorem completelyPositive_comp_local
    {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    {Phi : Operator H →ₗ[Complex] Operator K}
    {Psi : Operator K →ₗ[Complex] Operator L}
    (hPhi : CompletelyPositive Phi) (hPsi : CompletelyPositive Psi) :
    CompletelyPositive (Psi.comp Phi) := by
  intro n M hM
  exact hPsi n (OperatorMatrix.map Phi M) (hPhi n M hM)
theorem signedHRawLinear_completelyPositive
    (sign : BK05WordPolarity) : CompletelyPositive (signedHRawLinear sign) := by
  cases sign <;> exact hadamardTransport.completelyPositive_conjOperator
theorem signedKRawLinear_completelyPositive
    (sign : BK05WordPolarity) : CompletelyPositive (signedKRawLinear sign) := by
  cases sign with
  | normal => exact phaseTransport.completelyPositive_conjOperator
  | inverse => exact phaseTransport.symm.completelyPositive_conjOperator
theorem phaseCycleTargetChannel_completelyPositive
    (q : Nat) (target : ZMod q) :
    CompletelyPositive (phaseCycleTargetChannel q target) := by
  simpa [phaseCycleTargetChannel] using
    (OneQubitMagic.phaseShiftTransport
      (phaseCycleAngle q * target.val)).completelyPositive_conjOperator
theorem hFixedIdealLetterLinear_completelyPositive
    (letter : BK05SignedPhaseLetter (-Real.pi / 4)) :
    CompletelyPositive (hFixedIdealLetterLinear letter) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .normal
      | k => exact signedKRawLinear_completelyPositive .normal
      | phase => exact phaseCycleTargetChannel_completelyPositive 8 (hPhaseTarget .normal)
  | negative atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .inverse
      | k => exact signedKRawLinear_completelyPositive .inverse
      | phase => exact phaseCycleTargetChannel_completelyPositive 8 (hPhaseTarget .inverse)
theorem hFixedIdealWordLinear_completelyPositive :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hFixedIdealWordLinear letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hFixedIdealWordLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons letter tail ih =>
      simpa [hFixedIdealWordLinear] using
        completelyPositive_comp_local ih
          (hFixedIdealLetterLinear_completelyPositive letter)
theorem tFixedIdealLetterLinear_completelyPositive
    (letter : BK05SignedPhaseLetter (-Real.pi / 6)) :
    CompletelyPositive (tFixedIdealLetterLinear letter) := by
  cases letter with
  | positive atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .normal
      | k => exact signedKRawLinear_completelyPositive .normal
      | phase => exact phaseCycleTargetChannel_completelyPositive 12 (tPhaseTarget .normal)
  | negative atom =>
      cases atom with
      | h => exact signedHRawLinear_completelyPositive .inverse
      | k => exact signedKRawLinear_completelyPositive .inverse
      | phase => exact phaseCycleTargetChannel_completelyPositive 12 (tPhaseTarget .inverse)
theorem tFixedIdealWordLinear_completelyPositive :
    ∀ letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive (tFixedIdealWordLinear letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tFixedIdealWordLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons letter tail ih =>
      simpa [tFixedIdealWordLinear] using
        completelyPositive_comp_local ih
          (tFixedIdealLetterLinear_completelyPositive letter)
noncomputable def hFixedIdealWordChannel
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
    QuantumChannel QubitSpace QubitSpace where
  toLinearMap := hFixedIdealWordLinear letters
  completely_positive := hFixedIdealWordLinear_completelyPositive letters
  trace_preserving := hFixedIdealWordLinear_trace letters
noncomputable def tFixedIdealWordChannel
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
    QuantumChannel QubitSpace QubitSpace where
  toLinearMap := tFixedIdealWordLinear letters
  completely_positive := tFixedIdealWordLinear_completelyPositive letters
  trace_preserving := tFixedIdealWordLinear_trace letters
noncomputable def hIdealWordKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :=
  channelKraus (hFixedIdealWordChannel letters)
noncomputable def tIdealWordKraus
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :=
  channelKraus (tFixedIdealWordChannel letters)
theorem hRetryTargetHitLinear_completelyPositive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    forall (remaining : Nat) (position : ZMod 8),
      CompletelyPositive (hRetryTargetHitLinear h target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [hRetryTargetHitLinear, htarget] using
          completelyPositive_add_local
            (completelyPositive_comp_local (hStepLinear_completelyPositive h true)
              (ih (position + 1)))
            (completelyPositive_comp_local (hStepLinear_completelyPositive h false)
              (ih (position - 1)))
theorem hRetryPhaseExhaustedLinear_completelyPositive
    (h : DensityOperator QubitSpace) (target : ZMod 8) :
    forall (remaining : Nat) (position : ZMod 8),
      CompletelyPositive
        (hRetryPhaseExhaustedLinear h target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [hRetryPhaseExhaustedLinear, htarget] using
          completelyPositive_add_local
            (completelyPositive_comp_local (hStepLinear_completelyPositive h true)
              (ih (position + 1)))
            (completelyPositive_comp_local (hStepLinear_completelyPositive h false)
              (ih (position - 1)))
theorem hWordLiveLinear_completelyPositive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hWordLiveLinear h blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hWordLiveLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons head tail ih =>
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [hWordLiveLinear]
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (hRetryTargetHitLinear_completelyPositive h
            (hPhaseTarget .normal) (8 * blocks) 0)
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (hRetryTargetHitLinear_completelyPositive h
            (hPhaseTarget .inverse) (8 * blocks) 0)
theorem hWordPhaseStoppedLinear_completelyPositive
    (h : DensityOperator QubitSpace) (blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 4)),
      CompletelyPositive (hWordPhaseStoppedLinear h blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [hWordPhaseStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := hWordLiveLinear_completelyPositive h blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [hWordPhaseStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (hRetryPhaseExhaustedLinear_completelyPositive h
              (hPhaseTarget .normal) (8 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (hRetryPhaseExhaustedLinear_completelyPositive h
              (hPhaseTarget .inverse) (8 * blocks) 0)) ih
theorem tSupplyStoppingComponentLinear_completelyPositive
    (t : DensityOperator QubitSpace)
    (nextTrue nextFalse onPairExhausted :
      Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (htrue : CompletelyPositive nextTrue)
    (hfalse : CompletelyPositive nextFalse)
    (hpair : CompletelyPositive onPairExhausted) :
    forall attempts : Nat,
      CompletelyPositive
        (tSupplyStoppingComponentLinear t attempts
          nextTrue nextFalse onPairExhausted) := by
  intro attempts
  induction attempts with
  | zero => simpa [tSupplyStoppingComponentLinear] using hpair
  | succ attempts ih =>
      simpa [tSupplyStoppingComponentLinear] using
        completelyPositive_add_local
          (completelyPositive_add_local
            (completelyPositive_comp_local
              (tAcceptedStepLinear_completelyPositive t true) htrue)
            (completelyPositive_comp_local
              (tAcceptedStepLinear_completelyPositive t false) hfalse))
          (completelyPositive_comp_local
            (tRejectStepLinear_completelyPositive t) ih)
theorem tRetryTargetHitLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryTargetHitLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryTargetHitLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
      · simpa [tRetryTargetHitLinear, tSupplyTargetHitLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryTargetHitLinear t pairAttempts target remaining (position + 1))
            (tRetryTargetHitLinear t pairAttempts target remaining (position - 1))
            (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
            pairAttempts
theorem tRetryPhaseExhaustedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryPhaseExhaustedLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_id_local (H := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPhaseExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPhaseExhaustedLinear, tSupplyPhaseExhaustedLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPhaseExhaustedLinear t pairAttempts target remaining (position - 1))
            (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
            pairAttempts
theorem tRetryPairExhaustedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts : Nat) (target : ZMod 12) :
    forall (remaining : Nat) (position : ZMod 12),
      CompletelyPositive
        (tRetryPairExhaustedLinear t pairAttempts target remaining position) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position
      simpa [tRetryPairExhaustedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | succ remaining ih =>
      intro position
      by_cases htarget : position = target
      · simpa [tRetryPairExhaustedLinear, htarget] using
          (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
      · simpa [tRetryPairExhaustedLinear, tSupplyPairExhaustedLinear,
          tSupplyStoppingComponentLinear, htarget] using
          tSupplyStoppingComponentLinear_completelyPositive t
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position + 1))
            (tRetryPairExhaustedLinear t pairAttempts target remaining (position - 1))
            (LinearMap.id : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (ih (position + 1)) (ih (position - 1))
            (completelyPositive_id_local (H := QubitSpace)) pairAttempts
theorem tWordLiveLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive (tWordLiveLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordLiveLinear] using
        (completelyPositive_id_local (H := QubitSpace))
  | cons head tail ih =>
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordLiveLinear]
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .normal)
      · exact completelyPositive_comp_local ih
          (tRetryTargetHitLinear_completelyPositive t pairAttempts
            (tPhaseTarget .normal) (12 * blocks) 0)
      · exact completelyPositive_comp_local ih
          (signedHRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (signedKRawLinear_completelyPositive .inverse)
      · exact completelyPositive_comp_local ih
          (tRetryTargetHitLinear_completelyPositive t pairAttempts
            (tPhaseTarget .inverse) (12 * blocks) 0)
theorem tWordPhaseStoppedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive
        (tWordPhaseStoppedLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordPhaseStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := tWordLiveLinear_completelyPositive t pairAttempts blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordPhaseStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPhaseExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .normal) (12 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPhaseExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .inverse) (12 * blocks) 0)) ih
theorem tWordPairStoppedLinear_completelyPositive
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    forall letters : List (BK05SignedPhaseLetter (-Real.pi / 6)),
      CompletelyPositive
        (tWordPairStoppedLinear t pairAttempts blocks letters) := by
  intro letters
  induction letters with
  | nil =>
      simpa [tWordPairStoppedLinear] using
        (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
  | cons head tail ih =>
      have hlive := tWordLiveLinear_completelyPositive t pairAttempts blocks tail
      cases head <;> rename_i atom <;> cases atom <;>
        simp only [tWordPairStoppedLinear]
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPairExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .normal) (12 * blocks) 0)) ih
      · exact ih
      · exact ih
      · exact completelyPositive_add_local
          (completelyPositive_comp_local hlive
            (tRetryPairExhaustedLinear_completelyPositive t pairAttempts
              (tPhaseTarget .inverse) (12 * blocks) 0)) ih
theorem exists_cpKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) :
    ∃ m : Nat, ∃ E : FiniteKrausFamily (Fin m) H K,
      E.inducedMap = Phi := by
  exact exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef Phi
    (stdChoiMatrix_posSemidef_of_completelyPositive Phi hPhi)
noncomputable def cpKrausSize
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) : Nat :=
  Classical.choose (exists_cpKraus Phi hPhi)
noncomputable def cpKraus
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (Phi : Operator H →ₗ[Complex] Operator K)
    (hPhi : CompletelyPositive Phi) :
    FiniteKrausFamily (Fin (cpKrausSize Phi hPhi)) H K :=
  Classical.choose (Classical.choose_spec (exists_cpKraus Phi hPhi))
noncomputable def paddedKraus
    {kappa H K : Type u} [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily kappa H K) :
    FiniteKrausFamily (Option kappa) H K where
  operator
    | none => 0
    | some i => E.operator i
noncomputable def krausSum
    {iota kappa H K : Type u} [Fintype iota] [Fintype kappa]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (E : FiniteKrausFamily iota H K) (F : FiniteKrausFamily kappa H K) :
    FiniteKrausFamily (Sum iota kappa) H K where
  operator
    | .inl i => E.operator i
    | .inr j => F.operator j
abbrev BK05TerminalIndex (liveSize phaseSize pairSize : Nat) :=
  Sum (Option (Fin liveSize))
    (Sum (Option (Fin phaseSize)) (Option (Fin pairSize)))
def terminalStatus {liveSize phaseSize pairSize : Nat} :
    BK05TerminalIndex liveSize phaseSize pairSize → BK05WordLeafStatus
  | .inl _ => .live
  | .inr (.inl _) => .stoppedPhaseExhausted
  | .inr (.inr _) => .stoppedTPairExhausted
noncomputable def terminalKraus
    (live phase pair : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hlive : CompletelyPositive live)
    (hphase : CompletelyPositive phase)
    (hpair : CompletelyPositive pair) :
    FiniteKrausFamily
      (BK05TerminalIndex (cpKrausSize live hlive)
        (cpKrausSize phase hphase) (cpKrausSize pair hpair))
      QubitSpace QubitSpace :=
  krausSum (paddedKraus (cpKraus live hlive))
    (krausSum (paddedKraus (cpKraus phase hphase))
      (paddedKraus (cpKraus pair hpair)))
noncomputable def hTerminalKraus
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :=
  terminalKraus
    (hWordLiveLinear h blocks letters)
    (hWordPhaseStoppedLinear h blocks letters)
    (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
    (hWordLiveLinear_completelyPositive h blocks letters)
    (hWordPhaseStoppedLinear_completelyPositive h blocks letters)
    (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace))
noncomputable def tTerminalKraus
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :=
  terminalKraus
    (tWordLiveLinear t pairAttempts blocks letters)
    (tWordPhaseStoppedLinear t pairAttempts blocks letters)
    (tWordPairStoppedLinear t pairAttempts blocks letters)
    (tWordLiveLinear_completelyPositive t pairAttempts blocks letters)
    (tWordPhaseStoppedLinear_completelyPositive t pairAttempts blocks letters)
    (tWordPairStoppedLinear_completelyPositive t pairAttempts blocks letters)
noncomputable def hWordErrorBudget
    (h : DensityOperator QubitSpace) (blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) : Real :=
  ((8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Nat) : Real) *
      traceNorm (h.toOperator - hMagicState.toOperator) +
    2 * ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters : Real) *
      (255 / 256 : Real) ^ blocks)
noncomputable def tWordErrorBudget
    (t : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
    (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) : Real :=
  ((2 * pairAttempts * 12 * blocks *
      BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Nat) : Real) *
      traceNorm (t.toOperator - tMagicState.toOperator) +
    2 *
      ((BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          (4095 / 4096 : Real) ^ blocks +
        (BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters : Real) *
          ((12 * blocks : Real) * (1 / 3 : Real) ^ pairAttempts))
structure BK05RegisterRawLeaf
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  status : BK05WordLeafStatus
  history : List Bool
  ledger : ResourceLedger BK05ResourceToken
  raw : Operator (QubitRegister Wire)
structure BK05CompiledAggregate
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  Branch : Type
  [branchFintype : Fintype Branch]
  family : FiniteKrausFamily Branch (QubitRegister Wire) (QubitRegister Wire)
  status : Branch → BK05WordLeafStatus
  ledger : Branch → ResourceLedger BK05ResourceToken
instance BK05CompiledAggregate.instBranchFintype
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire) : Fintype compiled.Branch :=
  compiled.branchFintype
noncomputable def BK05CompiledAggregate.aggregateRaw
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    Operator (QubitRegister Wire) :=
  compiled.family.inducedMap rho.toOperator
noncomputable def BK05CompiledAggregate.rawLeaf
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire))
    (branch : compiled.Branch) : BK05RegisterRawLeaf Wire where
  status := compiled.status branch
  history := []
  ledger := compiled.ledger branch
  raw := (compiled.family.operator branch).comp
    (rho.toOperator.comp (LinearMap.adjoint (compiled.family.operator branch)))
noncomputable def BK05CompiledAggregate.rawLeaves
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) :
    Multiset (BK05RegisterRawLeaf Wire) :=
  (Finset.univ : Finset compiled.Branch).1.map (compiled.rawLeaf rho)
noncomputable def BK05CompiledAggregate.computedLedgers
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire) :
    Multiset (ResourceLedger BK05ResourceToken) :=
  (Finset.univ : Finset compiled.Branch).1.map compiled.ledger
noncomputable def BK05CompiledAggregate.totalWeight
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (compiled : BK05CompiledAggregate Wire)
    (rho : DensityOperator (QubitRegister Wire)) : Real :=
  (LinearMap.trace Complex (QubitRegister Wire)
    (compiled.aggregateRaw rho)).re
inductive BK05WordCompilation where
  | h (resource : DensityOperator QubitSpace) (blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 4)))
  | t (resource : DensityOperator QubitSpace) (pairAttempts blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 6)))
noncomputable def BK05WordCompilation.targetGate :
    BK05WordCompilation → UnitaryGate (Fin 2)
  | .h _ _ letters => BK05SignedPhaseLetter.evalList (-Real.pi / 4) letters
  | .t _ _ _ letters => BK05SignedPhaseLetter.evalList (-Real.pi / 6) letters
noncomputable def BK05WordCompilation.localErrorBudget :
    BK05WordCompilation → Real
  | .h resource blocks letters => hWordErrorBudget resource blocks letters
  | .t resource pairAttempts blocks letters =>
      tWordErrorBudget resource pairAttempts blocks letters
def BK05WordCompilation.computedLedger :
    BK05WordCompilation → ResourceLedger BK05ResourceToken
  | .h _ blocks letters =>
      Multiset.replicate
        (8 * blocks * BK05SignedPhaseLetter.resourceCount (-Real.pi / 4) letters) .h
  | .t _ pairAttempts blocks letters =>
      Multiset.replicate
        (2 * pairAttempts * 12 * blocks *
          BK05SignedPhaseLetter.resourceCount (-Real.pi / 6) letters) .t
noncomputable def compileWord
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) : BK05WordCompilation → BK05CompiledAggregate Wire
  | .h resource blocks letters =>
      { Branch := BK05TerminalIndex
          (cpKrausSize (hWordLiveLinear resource blocks letters)
            (hWordLiveLinear_completelyPositive resource blocks letters))
          (cpKrausSize (hWordPhaseStoppedLinear resource blocks letters)
            (hWordPhaseStoppedLinear_completelyPositive resource blocks letters))
          (cpKrausSize (0 : Operator QubitSpace →ₗ[Complex] Operator QubitSpace)
            (completelyPositive_zero_local (H := QubitSpace) (K := QubitSpace)))
        branchFintype := inferInstance
        family := selectedWireKraus wire (hTerminalKraus resource blocks letters)
        status := terminalStatus
        ledger := fun _ =>
          BK05WordCompilation.computedLedger (.h resource blocks letters) }
  | .t resource pairAttempts blocks letters =>
      { Branch := BK05TerminalIndex
          (cpKrausSize (tWordLiveLinear resource pairAttempts blocks letters)
            (tWordLiveLinear_completelyPositive resource pairAttempts blocks letters))
          (cpKrausSize (tWordPhaseStoppedLinear resource pairAttempts blocks letters)
            (tWordPhaseStoppedLinear_completelyPositive resource pairAttempts blocks letters))
          (cpKrausSize (tWordPairStoppedLinear resource pairAttempts blocks letters)
            (tWordPairStoppedLinear_completelyPositive resource pairAttempts blocks letters))
        branchFintype := inferInstance
        family := selectedWireKraus wire
          (tTerminalKraus resource pairAttempts blocks letters)
        status := terminalStatus
        ledger := fun _ =>
          BK05WordCompilation.computedLedger
            (.t resource pairAttempts blocks letters) }
noncomputable def selectedWireErrorScale
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) : Real :=
  (Fintype.card
      ((((Fin 2) × Bitstring (OtherWires wire)) ×
        ((Fin 2) × Bitstring (OtherWires wire)))) : Real) *
    ((Fintype.card ((Fin 2) × (Fin 2)) : Real) * 16)
noncomputable def compileWordRegisterErrorBound
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (wire : Wire) (spec : BK05WordCompilation) : Real :=
  selectedWireErrorScale wire * spec.localErrorBudget
def BK05WordLeafStatus.thenStatus :
    BK05WordLeafStatus → BK05WordLeafStatus → BK05WordLeafStatus
  | .live, suffix => suffix
  | .stoppedPhaseExhausted, _ => .stoppedPhaseExhausted
  | .stoppedTPairExhausted, _ => .stoppedTPairExhausted
noncomputable def BK05CompiledAggregate.seq
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (first second : BK05CompiledAggregate Wire) :
    BK05CompiledAggregate Wire where
  Branch := first.Branch × second.Branch
  branchFintype := inferInstance
  family := krausSeq first.family second.family
  status branch := (first.status branch.1).thenStatus (second.status branch.2)
  ledger branch := first.ledger branch.1 + second.ledger branch.2
noncomputable def finiteUnitaryKraus
    {n : Type} [Fintype n] [DecidableEq n]
    (gate : UnitaryGate n) :
    FiniteKrausFamily Unit (EuclideanSpace Complex n)
      (EuclideanSpace Complex n) where
  operator _ := Matrix.toEuclideanLin
    (gate : Matrix n n Complex)
noncomputable def registerUnitaryKraus
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) :
    FiniteKrausFamily Unit (QubitRegister Wire) (QubitRegister Wire) :=
  finiteUnitaryKraus gate
noncomputable def exactGateAggregate
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (gate : UnitaryGate (Bitstring Wire)) : BK05CompiledAggregate Wire where
  Branch := Unit
  branchFintype := inferInstance
  family := registerUnitaryKraus gate
  status _ := .live
  ledger _ := 0
inductive BK05PhysicalRegisterCircuit
    (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | identity : BK05PhysicalRegisterCircuit Wire
  | word (wire : Wire) (spec : BK05WordCompilation) :
      BK05PhysicalRegisterCircuit Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      BK05PhysicalRegisterCircuit Wire
  | compose (first second : BK05PhysicalRegisterCircuit Wire) :
      BK05PhysicalRegisterCircuit Wire
noncomputable def BK05PhysicalRegisterCircuit.targetCircuit
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → FiniteRegisterCircuit Wire
  | .identity => .identity
  | .word wire spec => .oneQubit wire spec.targetGate
  | .xor control target hdistinct => .xor control target hdistinct
  | .compose first second =>
      .compose first.targetCircuit second.targetCircuit
noncomputable def BK05PhysicalRegisterCircuit.errorBudget
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → Real
  | .identity => 0
  | .word wire spec => compileWordRegisterErrorBound wire spec
  | .xor _ _ _ => 0
  | .compose first second => first.errorBudget + second.errorBudget
noncomputable def compileFiniteRegisterCircuit
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → BK05CompiledAggregate Wire
  | .identity => exactGateAggregate 1
  | .word wire spec => compileWord wire spec
  | .xor control target hdistinct =>
      exactGateAggregate (registerXorGate control target hdistinct)
  | .compose first second =>
      (compileFiniteRegisterCircuit first).seq
        (compileFiniteRegisterCircuit second)
noncomputable def BK05PhysicalRegisterCircuit.idealAggregate
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → BK05CompiledAggregate Wire
  | .identity => exactGateAggregate 1
  | .word wire spec => exactGateAggregate (singleQubitLift wire spec.targetGate)
  | .xor control target hdistinct =>
      exactGateAggregate (registerXorGate control target hdistinct)
  | .compose first second => first.idealAggregate.seq second.idealAggregate
inductive BK05RegisterAtom
    (theta : Real) (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | oneQubit (wire : Wire) (atom : BK05PhaseAtom theta) :
      BK05RegisterAtom theta Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      BK05RegisterAtom theta Wire
noncomputable def BK05RegisterAtom.eval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05RegisterAtom theta Wire → UnitaryGate (Bitstring Wire)
  | .oneQubit wire atom => singleQubitLift wire (atom.eval theta)
  | .xor control target hdistinct => registerXorGate control target hdistinct
inductive BK05RegisterWord
    (theta : Real) (Wire : Type) [Fintype Wire] [DecidableEq Wire] where
  | one : BK05RegisterWord theta Wire
  | atom (gate : BK05RegisterAtom theta Wire) : BK05RegisterWord theta Wire
  | mul (left right : BK05RegisterWord theta Wire) : BK05RegisterWord theta Wire
  | inverse (word : BK05RegisterWord theta Wire) : BK05RegisterWord theta Wire
noncomputable def BK05RegisterWord.eval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05RegisterWord theta Wire → UnitaryGate (Bitstring Wire)
  | .one => 1
  | .atom registerAtom => registerAtom.eval
  | .mul left right => left.eval * right.eval
  | .inverse word => word.eval⁻¹
noncomputable def BK05RegisterWord.orientedEval
    {theta : Real} {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (word : BK05RegisterWord theta Wire) :
    BK05WordPolarity → UnitaryGate (Bitstring Wire)
  | .normal => word.eval
  | .inverse => word.eval⁻¹
def BK05SignedPhaseLetter.ofPolarity
    {theta : Real} (atom : BK05PhaseAtom theta) :
    BK05WordPolarity → BK05SignedPhaseLetter theta
  | .normal => .positive atom
  | .inverse => .negative atom
noncomputable def BK05RegisterWord.compileH
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (blocks : Nat) :
    BK05RegisterWord (-Real.pi / 4) Wire → BK05WordPolarity →
      BK05PhysicalRegisterCircuit Wire
  | .one, _ => .identity
  | .atom (.oneQubit wire phaseAtom), polarity =>
      .word wire (.h resource blocks
        [BK05SignedPhaseLetter.ofPolarity phaseAtom polarity])
  | .atom (.xor control target hdistinct), _ =>
      .xor control target hdistinct
  | .mul left right, .normal =>
      .compose (right.compileH resource blocks .normal)
        (left.compileH resource blocks .normal)
  | .mul left right, .inverse =>
      .compose (left.compileH resource blocks .inverse)
        (right.compileH resource blocks .inverse)
  | .inverse word, polarity => word.compileH resource blocks polarity.flip
noncomputable def BK05RegisterWord.compileT
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (resource : DensityOperator QubitSpace) (pairAttempts blocks : Nat) :
    BK05RegisterWord (-Real.pi / 6) Wire → BK05WordPolarity →
      BK05PhysicalRegisterCircuit Wire
  | .one, _ => .identity
  | .atom (.oneQubit wire phaseAtom), polarity =>
      .word wire (.t resource pairAttempts blocks
        [BK05SignedPhaseLetter.ofPolarity phaseAtom polarity])
  | .atom (.xor control target hdistinct), _ =>
      .xor control target hdistinct
  | .mul left right, .normal =>
      .compose (right.compileT resource pairAttempts blocks .normal)
        (left.compileT resource pairAttempts blocks .normal)
  | .mul left right, .inverse =>
      .compose (left.compileT resource pairAttempts blocks .inverse)
        (right.compileT resource pairAttempts blocks .inverse)
  | .inverse word, polarity =>
      word.compileT resource pairAttempts blocks polarity.flip
inductive BK05PhysicalRegisterCircuit.SourceCertified
    (rho : DensityOperator QubitSpace)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire] :
    BK05PhysicalRegisterCircuit Wire → Prop where
  | identity : SourceCertified rho .identity
  | hWord (wire : Wire) (rounds blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 4))) :
      SourceCertified rho
        (.word wire (.h
          (BK15.Threshold.bk15AcceptedRunHOutput rho rounds) blocks letters))
  | tWord (wire : Wire)
      (hthreshold : tInitialError rho < BK05T.bk05TThreshold)
      (rounds pairAttempts blocks : Nat)
      (letters : List (BK05SignedPhaseLetter (-Real.pi / 6))) :
      SourceCertified rho
        (.word wire (.t
          (BK05TSemanticSchedule.rootOutput
            (bk05TCompleteSemanticSchedule rho hthreshold rounds))
          pairAttempts blocks letters))
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      SourceCertified rho (.xor control target hdistinct)
  | compose {first second : BK05PhysicalRegisterCircuit Wire}
      (hfirst : SourceCertified rho first)
      (hsecond : SourceCertified rho second) :
      SourceCertified rho (.compose first second)
def BK05OperationalApproximation
    (rho : DensityOperator QubitSpace)
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    (circuit : FiniteRegisterCircuit Wire) (precision : Real) : Prop :=
  ∃ (representative : UnitaryGate (Bitstring Wire))
      (physical : BK05PhysicalRegisterCircuit Wire),
    GlobalPhaseEquivalent circuit.unitary representative ∧
    ‖(physical.targetCircuit.unitary :
        Matrix (Bitstring Wire) (Bitstring Wire) Complex) -
      (representative : Matrix (Bitstring Wire) (Bitstring Wire) Complex)‖ <
        precision ∧
    physical.SourceCertified rho ∧
    (compileFiniteRegisterCircuit physical).family.Complete ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      (compileFiniteRegisterCircuit physical).totalWeight input = 1) ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      ((compileFiniteRegisterCircuit physical).rawLeaves input).map
          BK05RegisterRawLeaf.ledger =
        (compileFiniteRegisterCircuit physical).computedLedgers) ∧
    ((∃ branch : (compileFiniteRegisterCircuit physical).Branch,
        (compileFiniteRegisterCircuit physical).status branch =
          .stoppedPhaseExhausted) ∧
      (∃ branch : (compileFiniteRegisterCircuit physical).Branch,
        (compileFiniteRegisterCircuit physical).status branch =
          .stoppedTPairExhausted)) ∧
    (∀ input : DensityOperator (QubitRegister Wire),
      traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw input -
            physical.idealAggregate.aggregateRaw input) < precision) ∧
    ∀ input : DensityOperator (QubitRegister Wire),
      traceNorm
          ((compileFiniteRegisterCircuit physical).aggregateRaw input -
            (exactGateAggregate circuit.unitary).aggregateRaw input) < precision
def BK05AdaptiveUniversal (rho : DensityOperator QubitSpace) : Prop :=
  ∀ {Wire : Type} [Fintype Wire] [DecidableEq Wire] [Nonempty Wire]
    (circuit : FiniteRegisterCircuit Wire) (precision : Real),
    0 < precision → BK05OperationalApproximation rho circuit precision
end Distillation
end QEC


