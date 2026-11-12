-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
-- name    : QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:41:39.735481+00:00
-- url     : https://prove2.me/theorems/e77d75be-537f-4015-8145-cfb96f12a57b
-- title:
--   Syndrome Decoding
-- statement:
--   Definitions and structural lemmas for Syndrome Decoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerSyndrome_map_properties
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_one
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
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
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_hh18PhysicalTInvBranch_eq_logicalT
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
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
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
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


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
abbrev PhysicalSite := HH18PuncturedReedMuller.PhysicalSite 4 0
abbrev LogicalSite := HH18PuncturedReedMuller.LogicalSite 4 0
abbrev PhysicalRegister := QubitRegister PhysicalSite
abbrev LogicalRegister := QubitRegister LogicalSite
abbrev PhysicalErrorWord := HH18NoisyInput.PhysicalErrorWord 4 0
abbrev InjectionOutcomeWord := HH18SitewisePhaseInjection.InjectionOutcomeWord
abbrev CheckIndex :=
  Sum (HH18PuncturedReedMuller.ZCheckIndex 0 1 4)
    (HH18PuncturedReedMuller.XCheckIndex 0 1 4)
abbrev Syndrome := JointSyndrome CheckIndex
def errorPauli (error : PhysicalErrorWord) : Binary PhysicalSite :=
  cssZCheck error
def measuredSyndrome (error : PhysicalErrorWord) : Syndrome :=
  fun check =>
    if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then
      StabilizerOutcome.positive
    else
      StabilizerOutcome.negative
def Accepts (error : PhysicalErrorWord) : Prop :=
  measuredSyndrome error =
    HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4
theorem accepts_iff_zero_syndrome (error : PhysicalErrorWord) :
    Accepts error ↔
      stabilizerSyndrome
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (errorPauli error) = 0 := by
  constructor
  · intro haccept
    funext check
    change stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0
    have hcheck := congrFun haccept check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive at hcheck
    by_cases hbit : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0
    · exact hbit
    · simp [hbit] at hcheck
  · intro hzero
    funext check
    change (if stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 then StabilizerOutcome.positive
      else StabilizerOutcome.negative) = StabilizerOutcome.positive
    have hcheck : stabilizerSyndromeBit
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (errorPauli error) = 0 := by
      exact congrFun hzero check
    simp [hcheck]
def fullSyndromeInstrument :
    FiniteInstrument Syndrome Syndrome PhysicalRegister PhysicalRegister :=
  jointStabilizerInstrument
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
noncomputable def errorBranchOperator (error : PhysicalErrorWord) :
    Operator PhysicalRegister :=
  (InnerProductSpace.rankOne Complex
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)
    (HH18NoisyInput.hh18PhysicalTInvErrorBranch error)).toLinearMap
noncomputable def injectedBranchOperator
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  (InnerProductSpace.rankOne Complex
    (HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt error outcomes
      HH18NoisyInput.hh18EncodedLogicalPlusInput)
    (HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt error outcomes
      HH18NoisyInput.hh18EncodedLogicalPlusInput)).toLinearMap
theorem idealBranch_mem_encodedCarrier :
    HH18NoisyInput.hh18PhysicalTInvBranch ∈
      HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier := by
  rw [HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT]
  exact HH18NoisyInput.hh18_15_1_0_encodedCode.encode_mem _
noncomputable def rawSyndromeBranch
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (syndrome : Syndrome) : Operator PhysicalRegister :=
  fullSyndromeInstrument.branchOperator syndrome
    (injectedBranchOperator error outcomes)
noncomputable def rawAcceptedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  rawSyndromeBranch error outcomes
    (HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4)
noncomputable def rawRejectedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    Operator PhysicalRegister :=
  ∑ syndrome : Syndrome,
    if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 then
      0
    else
      rawSyndromeBranch error outcomes syndrome
theorem hh18PureZMinimumDistance :
    MinimumDistance (HH18PuncturedReedMuller.xCode 0 1 4).dual 3 := by
  have hcarrier :
      (shortenedReedMullerCode 1 4 0).dual.carrier =
        (puncturedReedMullerCode 2 4 0).carrier := by
    simpa using
      (shortenedReedMullerCode_dual_eq_punctured_of_lt_of_le
        (m := 4) (r := 2) (w := 0) (by omega) (by omega))
  have hminimum := puncturedReedMullerCode_minimumDistance
    (m := 4) (r := 2) (w := 0) (by omega)
  have htail : binomialTail (4 - 2) 0 = 3 := by decide +kernel
  rcases hminimum with ⟨word, hword, hwordNonzero, hwordWeight, hleast⟩
  refine ⟨word, ?_, hwordNonzero, ?_, ?_⟩
  · rw [HH18PuncturedReedMuller.xCode_eq_shortened, hcarrier]
    exact hword
  · simpa only [htail] using hwordWeight
  · intro candidate hcandidate hcandidateNonzero
    have hcandidatePunctured :
        candidate ∈ (puncturedReedMullerCode 2 4 0).carrier := by
      rw [← hcarrier]
      simpa only [HH18PuncturedReedMuller.xCode_eq_shortened] using hcandidate
    simpa only [htail] using
      hleast candidate hcandidatePunctured hcandidateNonzero
theorem acceptedError_eq_zero_of_hammingWeight_lt_three (error : PhysicalErrorWord)
    (hweight : HammingWeight error < 3) (haccept : Accepts error) :
    error = 0 := by
  by_contra herror
  obtain ⟨x, hx, hnotCommutes⟩ :=
    exists_x_check_not_commutes_cssZCheck_of_hammingWeight_lt_dualMinimumDistance
      (HH18PuncturedReedMuller.xCode 0 1 4)
      hh18PureZMinimumDistance herror hweight
  have hzero := (accepts_iff_zero_syndrome error).1 haccept
  have hnormalizer : InStabilizerNormalizer
      (HH18PuncturedReedMuller.checkGenerator 0 1 4)
      (errorPauli error) :=
    (stabilizerSyndrome_map_properties
      (HH18PuncturedReedMuller.checkGenerator 0 1 4)
      (errorPauli error) (errorPauli error) (errorPauli error)).1.mp hzero
  have hgenerated : GeneratedStabilizer
      (HH18PuncturedReedMuller.checkGenerator 0 1 4) (cssXCheck x) := by
    change GeneratedStabilizer
      (binaryCSSParityCheckGenerators
        (HH18PuncturedReedMuller.zParityCheck 0 1 4)
        (HH18PuncturedReedMuller.xParityCheck 0 1 4))
      (cssXCheck x)
    apply binaryCSSParityCheckGenerators_generate_cssXCheck
    simpa only [HH18PuncturedReedMuller.xCode] using hx
  exact hnotCommutes (by
    simpa only [errorPauli] using hnormalizer (cssXCheck x) hgenerated)
theorem correctableAcceptedError_eq_zero (error : PhysicalErrorWord)
    (hweight : HammingWeight error ≤ 1) (haccept : Accepts error) :
    error = 0 :=
  acceptedError_eq_zero_of_hammingWeight_lt_three error (by omega) haccept
theorem zeroErrorBranch_eq_ideal :
    HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord) =
      HH18NoisyInput.hh18PhysicalTInvBranch := by
  rw [HH18NoisyInput.hh18PhysicalTInvErrorBranch,
    HH18NoisyInput.zErrorOperator]
  change toQubitOperator (binaryOne (ι := PhysicalSite))
      HH18NoisyInput.hh18PhysicalTInvBranch =
    HH18NoisyInput.hh18PhysicalTInvBranch
  rw [toQubitOperator_one]
  rfl
noncomputable def correctableAcceptedCarrierState
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) :
    HH18NoisyInput.hh18_15_1_0_encodedCode.code.carrier :=
  ⟨HH18NoisyInput.hh18PhysicalTInvErrorBranch error, by
    have hzero := correctableAcceptedError_eq_zero error hweight haccept
    subst error
    rw [zeroErrorBranch_eq_ideal]
    exact idealBranch_mem_encodedCarrier⟩
noncomputable def decodedCorrectableAcceptedOutput
    (error : PhysicalErrorWord) (hweight : HammingWeight error ≤ 1)
    (haccept : Accepts error) : LogicalRegister :=
  HH18NoisyInput.hh18_15_1_0_encodedCode.encoding.symm
    (correctableAcceptedCarrierState error hweight haccept)
end HH18SyndromeDecoding
end Distillation
end QEC


