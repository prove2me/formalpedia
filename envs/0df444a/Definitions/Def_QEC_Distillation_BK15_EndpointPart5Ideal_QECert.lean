-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart5Ideal_QECert
-- name    : QEC_Distillation_BK15_EndpointPart5Ideal_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T12:42:16.896066+00:00
-- url     : https://prove2.me/theorems/64c52cd5-98d6-47e9-95c5-ff51fa57e134
-- title:
--   BK15 ideal accepted-history exact norm sum
-- statement:
--   Source-exact ideal accepted-history normalization used by the BK15 endpoint proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

import Definitions.Def_QEC_Distillation_BK15_EndpointPart3_QECert
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
set_option maxRecDepth 262144 in
private theorem sum_historyKraus_norm_sq (psi : BK15Register) :
    ∑ history : History, ‖historyKraus history psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  classical
  have hcomplete := historyKrausFamily_complete
  change (∑ history : History,
      (LinearMap.adjoint (historyKraus history)).comp
        (historyKraus history)) = 1 at hcomplete
  have hinner :
      ∑ history : History,
        inner Complex (historyKraus history psi) (historyKraus history psi) =
      inner Complex psi psi := by
    calc
      ∑ history : History,
          inner Complex (historyKraus history psi) (historyKraus history psi) =
        ∑ history : History,
          inner Complex psi
            ((LinearMap.adjoint (historyKraus history)).comp
              (historyKraus history) psi) := by
            apply Finset.sum_congr rfl
            intro history _
            rw [LinearMap.comp_apply]
            exact (LinearMap.adjoint_inner_right
              (historyKraus history) psi (historyKraus history psi)).symm
      _ = inner Complex psi
          ((∑ history : History,
            (LinearMap.adjoint (historyKraus history)).comp
              (historyKraus history)) psi) := by
            rw [LinearMap.sum_apply, inner_sum]
      _ = inner Complex psi psi := by
            rw [LinearMap.congr_fun hcomplete psi]
            simp
  calc
    ∑ history : History, ‖historyKraus history psi‖ ^ 2 =
        ∑ history : History,
          (inner Complex (historyKraus history psi)
            (historyKraus history psi)).re := by
              apply Finset.sum_congr rfl
              intro history _
              rw [inner_self_eq_norm_sq_to_K]
              simp [pow_two, Complex.mul_re]
    _ = (∑ history : History,
          inner Complex (historyKraus history psi)
            (historyKraus history psi)).re := by
              rw [Complex.re_sum]
    _ = (inner Complex psi psi).re := congrArg Complex.re hinner
    _ = ‖psi‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [pow_two, Complex.mul_re]
private theorem zeroErrorWord_norm_sq :
    ‖bk15ErrorWordState zeroErrorWord‖ ^ 2 = 1 := by
  rw [← bk15AErrorBasis_apply zeroErrorWord]
  have hnorm : ‖bk15AErrorBasis zeroErrorWord‖ = 1 :=
    bk15AErrorBasis.norm_eq_one zeroErrorWord
  rw [hnorm]
  norm_num
theorem sum_ideal_acceptedHistory_norm_sq_QECertEndpoint :
    ∑ zOutcome : ZJointSyndrome,
      ‖historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord)‖ ^ 2 = 1 := by
  classical
  calc
    ∑ zOutcome : ZJointSyndrome,
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2 =
      ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        ‖historyKraus (zOutcome, xOutcome)
          (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro zOutcome _
            rw [Fintype.sum_eq_single
              (signSyndrome (0 : XCheckIndex → Bit))]
            · intro xOutcome hxOutcome
              rw [historyKraus_ideal_QECertEndpoint (zOutcome, xOutcome)]
              simp [hxOutcome]
    _ = ∑ history : History,
        ‖historyKraus history (bk15ErrorWordState zeroErrorWord)‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
    _ = ‖bk15ErrorWordState zeroErrorWord‖ ^ 2 :=
      sum_historyKraus_norm_sq (bk15ErrorWordState zeroErrorWord)
    _ = 1 := zeroErrorWord_norm_sq

end Recurrence
end BK15
end Distillation
end QEC
end
end


