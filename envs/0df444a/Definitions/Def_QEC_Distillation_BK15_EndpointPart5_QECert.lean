-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart5_QECert
-- name    : QEC_Distillation_BK15_EndpointPart5_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T12:48:39.66843+00:00
-- url     : https://prove2.me/theorems/6dbf55af-a9c0-4d42-aef5-412fd79e30bd
-- title:
--   BK15 accepted endpoint exact helper part 5
-- statement:
--   Source-exact checked intermediate declarations for the BK15 accepted endpoint formula.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

import Definitions.Def_QEC_Distillation_BK15_EndpointPart4_QECert
import Definitions.Def_QEC_Distillation_BK15_EndpointPart5Ideal_QECert
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
private theorem accepted_historyKraus_norm_sq (zOutcome : ZJointSyndrome)
    (error : Word) :
    ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error)‖ ^ 2 =
      if l1Syndrome error = 0 then
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2
      else 0 := by
  classical
  by_cases hsyndrome : l1Syndrome error = 0
  · rw [if_pos hsyndrome]
    rw [accepted_historyKraus_error_QECertEndpoint]
    simp only [hsyndrome, map_zero, signSyndrome]
    rw [norm_smul, binaryPhaseScalar_norm_QECertEndpoint, one_mul, cssZCheck_norm_sq_QECertEndpoint]
  · rw [if_neg hsyndrome]
    have hmatching : signSyndrome (l1Syndrome error) ≠
        signSyndrome (0 : XCheckIndex → Bit) := by
      intro hsign
      apply hsyndrome
      have := congrArg binarySyndrome hsign
      simpa using this
    rw [accepted_historyKraus_error_QECertEndpoint,
      historyKraus_ideal_QECertEndpoint (zOutcome, signSyndrome (l1Syndrome error))]
    simp [hmatching]
set_option maxRecDepth 65536 in
theorem accepted_history_mass_eq_l1Dual_indicator_QECertEndpoint (error : Word) :
    ∑ zOutcome : ZJointSyndrome,
      ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error)‖ ^ 2 =
      if error ∈ l1DualWords then 1 else 0 := by
  classical
  have hmembership : error ∈ l1DualWords ↔ l1Syndrome error = 0 := by
    rw [mem_l1DualWords_iff, l1_dual_carrier_eq_l1Syndrome_ker]
    rfl
  by_cases hsyndrome : l1Syndrome error = 0
  · have hmember : error ∈ l1DualWords := hmembership.mpr hsyndrome
    rw [if_pos hmember]
    calc
      ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error)‖ ^ 2 =
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro zOutcome _
              rw [accepted_historyKraus_norm_sq, if_pos hsyndrome]
      _ = 1 := sum_ideal_acceptedHistory_norm_sq_QECertEndpoint
  · have hnotmember : error ∉ l1DualWords := by
      intro hmember
      exact hsyndrome (hmembership.mp hmember)
    rw [if_neg hnotmember]
    calc
      ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error)‖ ^ 2 =
        ∑ _zOutcome : ZJointSyndrome, 0 := by
              apply Finset.sum_congr rfl
              intro zOutcome _
              rw [accepted_historyKraus_norm_sq, if_neg hsyndrome]
      _ = 0 := by simp

end Recurrence
end BK15
end Distillation
end QEC
end
end


