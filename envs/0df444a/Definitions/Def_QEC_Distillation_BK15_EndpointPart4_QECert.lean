-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart4_QECert
-- name    : QEC_Distillation_BK15_EndpointPart4_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:05:29.759549+00:00
-- url     : https://prove2.me/theorems/9ceaadfe-5d2e-41d7-b91e-9746a53cab81
-- title:
--   BK15 accepted endpoint exact helper part 4
-- statement:
--   Source-exact checked intermediate declarations for the BK15 accepted endpoint formula.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_BK15_Protocol_aWordCorrectionTransport_eigen
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
import Theorems.Thm_QEC_Distillation_BK15_l1_dimension
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_l1Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_l2Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_mem_l1DualWords_iff
import Theorems.Thm_QEC_Distillation_BK15_mem_l2_dual_iff_exists_l1_plus_allOnes
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
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
import Definitions.Def_QEC_Distillation_BK15_EndpointPart1_QECert
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
set_option maxHeartbeats 0 in
private theorem cssZCheck_xFactor_intertwines (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        jointStabilizerFactor xChecks
          (signSyndrome (l1Syndrome error)) check =
      jointStabilizerFactor xChecks
          (signSyndrome (0 : XCheckIndex → Bit)) check *
        toHermitianQubitOperator (cssZCheck error) := by
  let T := toHermitianQubitOperator (cssZCheck error)
  let S := toHermitianQubitOperator (xChecks check)
  let scalar := (signSyndrome (l1Syndrome error) check).sign
  have hcheck : T * S = scalar • (S * T) := by
    exact cssZCheck_xCheck_relation_QECertEndpoint error check
  have hscalar : scalar * scalar = 1 := by
    exact StabilizerOutcome.sign_mul_self
      (signSyndrome (l1Syndrome error) check)
  simp only [jointStabilizerFactor, stabilizerProjector, signSyndrome,
    bitToSign, StabilizerOutcome.sign, Pi.zero_apply, if_pos, one_smul]
  change T * ((1 / 2 : Complex) • (1 + scalar • S)) =
    ((1 / 2 : Complex) • (1 + S)) * T
  calc
    T * ((1 / 2 : Complex) • (1 + scalar • S)) =
        (1 / 2 : Complex) • (T + scalar • (T * S)) := by
          simp only [mul_smul_comm, mul_add, mul_one]
    _ = (1 / 2 : Complex) •
        (T + scalar • (scalar • (S * T))) := by rw [hcheck]
    _ = (1 / 2 : Complex) • (T + S * T) := by
      rw [smul_smul, hscalar, one_smul]
    _ = ((1 / 2 : Complex) • (1 + S)) * T := by
      simp only [smul_mul_assoc, add_mul, one_mul]
private theorem cssZCheck_xProjector_intertwines (error : Word) :
    toHermitianQubitOperator (cssZCheck error) *
        xProjector (signSyndrome (l1Syndrome error)) =
      xProjector (signSyndrome (0 : XCheckIndex → Bit)) *
        toHermitianQubitOperator (cssZCheck error) := by
  exact jointStabilizerProjector_intertwines_operator_QECertEndpoint
    xChecks xChecks_commute (toHermitianQubitOperator (cssZCheck error))
    (signSyndrome (l1Syndrome error))
    (signSyndrome (0 : XCheckIndex → Bit))
    (cssZCheck_xFactor_intertwines error)
private theorem cssZCheck_zCheck_commute (error : Word)
    (check : ZCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        toHermitianQubitOperator (zChecks check) =
      toHermitianQubitOperator (zChecks check) *
        toHermitianQubitOperator (cssZCheck error) := by
  have hcomm := toQubitOperator_commute_of_commutes
    (cssZCheck error) (cssZCheck (l2Generator check))
    (cssZCheck_commutes_cssZCheck _ _)
  simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using hcomm
private theorem cssZCheck_zFactor_commute (error : Word)
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        jointStabilizerFactor zChecks outcome check =
      jointStabilizerFactor zChecks outcome check *
        toHermitianQubitOperator (cssZCheck error) := by
  let T := toHermitianQubitOperator (cssZCheck error)
  let S := toHermitianQubitOperator (zChecks check)
  let scalar := (outcome check).sign
  have hcheck : T * S = S * T := cssZCheck_zCheck_commute error check
  simp only [jointStabilizerFactor, stabilizerProjector]
  change T * ((1 / 2 : Complex) • (1 + scalar • S)) =
    ((1 / 2 : Complex) • (1 + scalar • S)) * T
  calc
    T * ((1 / 2 : Complex) • (1 + scalar • S)) =
        (1 / 2 : Complex) • (T + scalar • (T * S)) := by
          simp only [mul_smul_comm, mul_add, mul_one]
    _ = (1 / 2 : Complex) • (T + scalar • (S * T)) := by rw [hcheck]
    _ = ((1 / 2 : Complex) • (1 + scalar • S)) * T := by
      simp only [smul_mul_assoc, add_mul, one_mul]
private theorem cssZCheck_zProjector_commute (error : Word)
    (outcome : ZJointSyndrome) :
    toHermitianQubitOperator (cssZCheck error) * zProjector outcome =
      zProjector outcome * toHermitianQubitOperator (cssZCheck error) := by
  exact jointStabilizerProjector_intertwines_operator_QECertEndpoint
    zChecks zChecks_commute (toHermitianQubitOperator (cssZCheck error))
    outcome outcome (cssZCheck_zFactor_commute error outcome)
private theorem historyCorrection_symm_cssZCheck (outcome : ZJointSyndrome)
    (error : Word) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ error) •
        (toHermitianQubitOperator (cssZCheck error) *
          (historyCorrection outcome).symm.toLinearEquiv.toLinearMap) := by
  change (aWordCorrectionTransport
      (l2SyndromeSection (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ error) •
        (toHermitianQubitOperator (cssZCheck error) *
          (aWordCorrectionTransport
            (l2SyndromeSection (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap)
  exact aWordCorrectionTransport_symm_cssZCheck_QECertEndpoint
    (l2SyndromeSection (zBinarySyndrome outcome)) error
private theorem cssZCheck_zeroErrorWord (error : Word) :
    toHermitianQubitOperator (cssZCheck error)
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState error := by
  simpa [zeroErrorWord] using cssZCheck_errorWord_QECertEndpoint error (0 : Word)
set_option maxRecDepth 65536 in
private theorem cssZCheck_zProjector_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    zProjector zOutcome
        (toHermitianQubitOperator (cssZCheck error)
          (bk15ErrorWordState zeroErrorWord)) =
      toHermitianQubitOperator (cssZCheck error)
        (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)) := by
  rw [← Module.End.mul_apply,
    (cssZCheck_zProjector_commute error zOutcome).symm,
    Module.End.mul_apply]
set_option maxRecDepth 65536 in
private theorem historyCorrection_cssZCheck_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
        (toHermitianQubitOperator (cssZCheck error)
          (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))) := by
  exact LinearMap.congr_fun
    (historyCorrection_symm_cssZCheck zOutcome error)
    (zProjector zOutcome (bk15ErrorWordState zeroErrorWord))
set_option maxRecDepth 65536 in
private theorem xProjector_zero_cssZCheck_zeroErrorWord_apply
    (zOutcome : ZJointSyndrome) (error : Word) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        (toHermitianQubitOperator (cssZCheck error)
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) =
      toHermitianQubitOperator (cssZCheck error)
        (xProjector (signSyndrome (l1Syndrome error))
          ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
            (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) := by
  exact LinearMap.congr_fun
    ((cssZCheck_xProjector_intertwines error).symm)
    ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
      (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))
set_option maxRecDepth 65536 in
private theorem historyKraus_apply_explicit
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome)
    (psi : BK15Register) :
    historyKraus (zOutcome, xOutcome) psi =
      xProjector xOutcome
        ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
          (zProjector zOutcome psi)) := by
  simp only [historyKraus, Module.End.mul_apply]
set_option maxRecDepth 65536 in
private theorem accepted_historyKraus_error_unfolded
    (zOutcome : ZJointSyndrome) (error : Word) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
          (zProjector zOutcome (bk15ErrorWordState error))) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          (xProjector (signSyndrome (l1Syndrome error))
            ((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap
              (zProjector zOutcome (bk15ErrorWordState zeroErrorWord)))) := by
  rw [← cssZCheck_zeroErrorWord error,
    cssZCheck_zProjector_zeroErrorWord_apply,
    historyCorrection_cssZCheck_zeroErrorWord_apply,
    map_smul,
    xProjector_zero_cssZCheck_zeroErrorWord_apply]
set_option maxRecDepth 65536 in
theorem accepted_historyKraus_error_QECertEndpoint (zOutcome : ZJointSyndrome)
    (error : Word) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) =
      binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) •
        toHermitianQubitOperator (cssZCheck error)
          (historyKraus
            (zOutcome, signSyndrome (l1Syndrome error))
            (bk15ErrorWordState zeroErrorWord)) := by
  rw [historyKraus_apply_explicit, historyKraus_apply_explicit]
  exact accepted_historyKraus_error_unfolded zOutcome error
theorem binaryPhaseScalar_norm_QECertEndpoint (phase : Bit) :
    ‖binaryPhaseScalar phase‖ = 1 := by
  by_cases hzero : phase = 0
  · rw [hzero, binaryPhaseScalar_zero]
    norm_num
  · rw [zmod_two_eq_one_of_ne_zero hzero, binaryPhaseScalar_one]
    norm_num
set_option maxRecDepth 65536 in
theorem cssZCheck_norm_sq_QECertEndpoint (error : Word) (psi : BK15Register) :
    ‖toHermitianQubitOperator (cssZCheck error) psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex)
      (toHermitianQubitOperator (cssZCheck error) psi),
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) psi]
  rw [(LinearMap.adjoint_inner_right
    (toHermitianQubitOperator (cssZCheck error)) psi
    (toHermitianQubitOperator (cssZCheck error) psi)).symm,
    adjoint_toHermitianQubitOperator_eq_self]
  have hsquare := LinearMap.congr_fun
    (toHermitianQubitOperator_square (cssZCheck error)) psi
  simp only [Module.End.mul_apply, Module.End.one_apply] at hsquare
  rw [hsquare, inner_self_eq_norm_sq_to_K]

end Recurrence
end BK15
end Distillation
end QEC
end
end


