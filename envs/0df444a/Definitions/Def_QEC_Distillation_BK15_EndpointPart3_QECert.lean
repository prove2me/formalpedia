-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart3_QECert
-- name    : QEC_Distillation_BK15_EndpointPart3_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:57:48.967806+00:00
-- url     : https://prove2.me/theorems/415de504-c07e-448b-a530-cf41c1a4dbf6
-- title:
--   BK15 accepted endpoint exact helper part 3
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
import Definitions.Def_QEC_Distillation_BK15_EndpointPart2_QECert
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
private theorem zeroZProjectedIdeal_zeroErrorWord :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord) =
      (32 : Complex)⁻¹ •
        ambientEncodingIsometry logicalNegativeAState := by
  simpa [zeroErrorWord] using zeroZProjectedIdeal_QECertEndpoint
private theorem historyCorrection_symm_ideal
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState zeroErrorWord := by
  change (aWordCorrectionTransport
    (l2SyndromeSection (zBinarySyndrome outcome))).symm
      (bk15ErrorWordState zeroErrorWord) = _
  rw [aWordCorrectionTransport_symm_eigen_QECertEndpoint]
  simp [zeroErrorWord, binaryPhaseScalar]
private theorem historyCorrection_symm_ideal_linear
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState zeroErrorWord := by
  exact historyCorrection_symm_ideal outcome
set_option maxRecDepth 65536 in
private theorem correctedZHistory_ideal
    (outcome : ZJointSyndrome) :
    ((historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        zProjector outcome) (bk15ErrorWordState zeroErrorWord) =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord) := by
  rw [historyCorrection_symm_zProjector_QECertEndpoint]
  simp only [Module.End.mul_apply]
  rw [historyCorrection_symm_ideal_linear]
private theorem encoded_xCheck_fixed
    (psi : LogicalRegister) (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check)
        (ambientEncodingIsometry psi) =
      ambientEncodingIsometry psi := by
  have hmem : ambientEncodingIsometry psi ∈ bk15EncodedCode.code.carrier := by
    change (bk15EncodedCode.encoding psi : BK15Register) ∈
      bk15EncodedCode.code.carrier
    exact (bk15EncodedCode.encoding psi).property
  have hP : xChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inl ⟨linearGenerator check,
      bk15CSSRows.evenRow_mem_evenCode check, rfl⟩
  have hfix := (mem_binaryCSSQuantumCodeOfDualLe_carrier
    bk15CSSRows.evenCode bk15CSSRows.rowCode.dual
    bk15CSSRows.cssDualContainment (ambientEncodingIsometry psi)).1 hmem
      (xChecks check) hP
  simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using hfix
private theorem encoded_xProjector_zero (psi : LogicalRegister) :
    xProjector (signSyndrome (0 : XCheckIndex → Bit))
        (ambientEncodingIsometry psi) =
      ambientEncodingIsometry psi := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (0 : XCheckIndex → Bit))
    (ambientEncodingIsometry psi)).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    encoded_xCheck_fixed psi check
private theorem xProjector_zeroProjectedIdeal
    (outcome : XJointSyndrome) :
    xProjector outcome
        (zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)) =
      if outcome = signSyndrome (0 : XCheckIndex → Bit) then
        zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)
      else 0 := by
  classical
  rw [zeroZProjectedIdeal_zeroErrorWord]
  by_cases houtcome : outcome = signSyndrome (0 : XCheckIndex → Bit)
  · rw [if_pos houtcome, houtcome]
    simp only [map_smul]
    rw [encoded_xProjector_zero]
  · rw [if_neg houtcome]
    have hmul := jointStabilizerProjector_mul_of_ne xChecks xChecks_commute
      outcome (signSyndrome (0 : XCheckIndex → Bit)) houtcome
    have happly := LinearMap.congr_fun hmul
      (ambientEncodingIsometry logicalNegativeAState)
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at happly
    change xProjector outcome
        (xProjector (signSyndrome (0 : XCheckIndex → Bit))
          (ambientEncodingIsometry logicalNegativeAState)) = 0 at happly
    rw [encoded_xProjector_zero] at happly
    simp only [map_smul]
    rw [happly, smul_zero]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem historyKraus_ideal_QECertEndpoint (history : History) :
    historyKraus history (bk15ErrorWordState zeroErrorWord) =
      if history.2 = signSyndrome (0 : XCheckIndex → Bit) then
        zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)
      else 0 := by
  rcases history with ⟨zOutcome, xOutcome⟩
  simp only [historyKraus, Module.End.mul_apply]
  change xProjector xOutcome
      (((historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
        zProjector zOutcome) (bk15ErrorWordState zeroErrorWord)) = _
  rw [correctedZHistory_ideal, xProjector_zeroProjectedIdeal]
theorem cssZCheck_xCheck_relation_QECertEndpoint (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (cssZCheck error) *
        toHermitianQubitOperator (xChecks check) =
      (signSyndrome (l1Syndrome error) check).sign •
        (toHermitianQubitOperator (xChecks check) *
          toHermitianQubitOperator (cssZCheck error)) := by
  have hHermitianZ :
      toHermitianQubitOperator (cssZCheck error) =
        toQubitOperator (cssZCheck error) := by
    simp [toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  have hHermitianX :
      toHermitianQubitOperator (xChecks check) =
        toQubitOperator (xChecks check) := by
    simp [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitianZ, hHermitianX]
  by_cases hpair : Coding.wordPairing error (linearGenerator check) = 0
  · have hdot : error ⬝ᵥ linearGenerator check = 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error = 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hcomm := cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
      hpair'
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = 1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    simpa [xChecks, cssZCheck, hsign] using hcomm.symm
  · have hdot : error ⬝ᵥ linearGenerator check ≠ 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error ≠ 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hnotcomm :
        ¬ Commutes (cssXCheck (linearGenerator check)) (cssZCheck error) := by
      simpa [cssXCheck, cssZCheck, Commutes,
        Coding.symplecticForm_x_zero_zero_z_eq_wordPairing] using hpair'
    have hanti := toQubitOperator_anticommute_of_not_commutes
      (cssXCheck (linearGenerator check)) (cssZCheck error) hnotcomm
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = -1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [neg_one_smul]
    calc
      toQubitOperator (cssZCheck error) *
          toQubitOperator (xChecks check) =
        -(- (toQubitOperator (cssZCheck error) *
          toQubitOperator (xChecks check))) := by simp
      _ = -(toQubitOperator (xChecks check) *
          toQubitOperator (cssZCheck error)) := by
        simpa [xChecks] using (congrArg Neg.neg hanti).symm

end Recurrence
end BK15
end Distillation
end QEC
end
end


