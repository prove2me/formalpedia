-- Prove2me | Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryIndicator_QECert
-- name    : QEC_Distillation_BK15_NegativeAHistoryIndicator_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T21:18:26.742376+00:00
-- url     : https://prove2.me/theorems/9bda152d-3e66-4407-b45a-c676d9b27501
-- title:
--   BK15 negative-A history indicator
-- statement:
--   Exact indicator identities used in the BK15 negative-A history sum.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean

import Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryEncoding_QECert
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
private theorem zeroZProjectedIdeal_zeroErrorWord_QECertNegativeAHistory :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (bk15ErrorWordState zeroErrorWord) =
      (32 : Complex)⁻¹ •
        ambientEncodingIsometry logicalNegativeAState := by
  simpa [zeroErrorWord] using zeroZProjectedIdeal_QECertNegativeAHistory

private theorem historyCorrection_symm_ideal
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState zeroErrorWord := by
  change (aWordCorrectionTransport
    (l2SyndromeSection (zBinarySyndrome outcome))).symm
      (bk15ErrorWordState zeroErrorWord) = _
  rw [aWordCorrectionTransport_symm_eigen_QECertNegativeAHistory]
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
  rw [historyCorrection_symm_zProjector_QECertNegativeAHistory]
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
  rw [zeroZProjectedIdeal_zeroErrorWord_QECertNegativeAHistory]
  by_cases houtcome : outcome = signSyndrome (0 : XCheckIndex → Bit)
  · rw [if_pos houtcome, houtcome]
    simp only [map_smul]
    rw [encoded_xProjector_zero]
  · rw [if_neg houtcome]
    have hmul := jointStabilizerProjector_mul_of_ne_QECertNegativeAHistorySupport xChecks xChecks_commute
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
private theorem historyKraus_ideal_QECertNegativeAHistory (history : History) :
    historyKraus history (bk15ErrorWordState zeroErrorWord) =
      if history.2 = signSyndrome (0 : XCheckIndex → Bit) then
        zProjector (signSyndrome (0 : ZCheckIndex → Bit))
          (bk15ErrorWordState zeroErrorWord)
      else 0 := by
  rcases history with ⟨zOutcome, xOutcome⟩
  simp only [historyKraus, Module.End.mul_apply]
  have h := correctedZHistory_ideal zOutcome
  simp only [Module.End.mul_apply] at h
  rw [h, xProjector_zeroProjectedIdeal]

private theorem cssZCheck_xCheck_relation (error : Word)
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
    exact cssZCheck_xCheck_relation error check
  have hscalar : scalar * scalar = 1 := by
    exact StabilizerOutcome.sign_mul_self
      (signSyndrome (l1Syndrome error) check)
  have hfactor : T * ((1 / 2 : Complex) • (1 + scalar • S)) =
      ((1 / 2 : Complex) • (1 + S)) * T := by
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
  simpa only [T, S, scalar, jointStabilizerFactor, stabilizerProjector,
    signSyndrome, bitToSign, StabilizerOutcome.sign, Pi.zero_apply, if_pos,
    one_smul] using hfactor

private theorem cssZCheck_xProjector_intertwines (error : Word) :
    toHermitianQubitOperator (cssZCheck error) *
        xProjector (signSyndrome (l1Syndrome error)) =
      xProjector (signSyndrome (0 : XCheckIndex → Bit)) *
        toHermitianQubitOperator (cssZCheck error) := by
  exact jointStabilizerProjector_intertwines_operator_QECertNegativeAHistory
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
  exact jointStabilizerProjector_intertwines_operator_QECertNegativeAHistory
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
  exact aWordCorrectionTransport_symm_cssZCheck_QECertNegativeAHistory
    (l2SyndromeSection (zBinarySyndrome outcome)) error

private theorem cssZCheck_zeroErrorWord (error : Word) :
    toHermitianQubitOperator (cssZCheck error)
        (bk15ErrorWordState zeroErrorWord) =
      bk15ErrorWordState error := by
  simpa [zeroErrorWord] using cssZCheck_errorWord_QECertNegativeAHistory error (0 : Word)

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
private theorem accepted_historyKraus_error_QECertNegativeAHistory (zOutcome : ZJointSyndrome)
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

end Recurrence
end BK15
end Distillation
end QEC
end
end

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
private theorem l2_coset_pairing_l2dual_decomposition
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit)
    (a : Fin 4 → Bit) (d : Bit) :
    Coding.wordPairing (l2CoefficientMap b + c • allOnes)
      (l1CoefficientMap a + d • allOnes) = c * d := by
  have hrows : ∀ (g : Sum (Fin 4) QuadraticIndex) (j : Fin 4),
      Coding.wordPairing (l2Generator g) (linearGenerator j) = 0 := by decide +kernel
  have hrowOnes : ∀ g : Sum (Fin 4) QuadraticIndex,
      Coding.wordPairing (l2Generator g) allOnes = 0 := by decide +kernel
  have honesRows : ∀ j : Fin 4,
      Coding.wordPairing allOnes (linearGenerator j) = 0 := by decide +kernel
  have hself : Coding.wordPairing allOnes allOnes = (1 : Bit) := by decide +kernel
  have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
    funext i
    change (∑ g, b g * l2Generator g i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ha : l1CoefficientMap a = ∑ j, a j • linearGenerator j := by
    funext i
    change (∑ j, a j * linearGenerator j i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb, ha]
  simp only [map_add, map_smul, map_sum, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, hrows, hrowOnes, honesRows,
    hself, smul_zero, zero_add, add_zero, Finset.sum_const_zero,
    smul_eq_mul, mul_one, mul_zero, mul_comm]

private theorem logicalAErrorState_label (c d : Bit) :
    logicalAErrorState c ((bitstringWordEquiv Unit).symm (fun _ => d)) =
      binaryPhaseScalar (c * d) *
        logicalNegativeAState ((bitstringWordEquiv Unit).symm (fun _ => d)) := by
  unfold logicalAErrorState
  change binaryPhaseScalar
      (c * (bitstringWordEquiv Unit
        ((bitstringWordEquiv Unit).symm (fun _ => d)) ())) *
        logicalNegativeAState ((bitstringWordEquiv Unit).symm (fun _ => d)) = _
  rw [Equiv.apply_symm_apply]

private theorem cssZCheck_l2_plus_allOnes_encoded
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit) :
    toHermitianQubitOperator (cssZCheck (l2CoefficientMap b + c • allOnes))
        (ambientEncodingIsometry logicalNegativeAState) =
      ambientEncodingIsometry (logicalAErrorState c) := by
  change toHermitianQubitOperator
      (cssZCheck (l2CoefficientMap b + c • allOnes))
      (bk15CSSRows.encoding bk15CSSRows_triorthogonal logicalNegativeAState :
        BK15Register) =
    (bk15CSSRows.encoding bk15CSSRows_triorthogonal (logicalAErrorState c) :
      BK15Register)
  ext bits
  simp [toHermitianQubitOperator, hermitianPhaseScalar, toQubitOperator,
    xSupport, zSupport, binaryOverlapCount, binaryOverlapSupport]
  by_cases hbits : bitstringWordEquiv (Fin 15) bits ∈
      bk15CSSRows.rowCode.dual.dual.carrier
  · have hsyndrome : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 :=
      l2Syndrome_eq_zero_of_mem_rowCode_doubleDual_QECertNegativeAHistory hbits
    have hdual : bitstringWordEquiv (Fin 15) bits ∈ L2.dual.carrier := by
      rw [l2_dual_carrier_eq_l2Syndrome_ker_QECertNegativeAHistorySupport]
      exact hsyndrome
    obtain ⟨a, d, had⟩ :=
      (mem_l2_dual_iff_exists_l1_plus_allOnes_QECertNegativeAHistorySupport
        (bitstringWordEquiv (Fin 15) bits)).1 hdual
    have hlabel :
        (bk15CSSRows.logicalBasisEquivLogicalQuotient
            bk15CSSRows_triorthogonal).symm
            (Submodule.Quotient.mk
              (⟨bitstringWordEquiv (Fin 15) bits, hbits⟩ :
                bk15CSSRows.rowCode.dual.dual.carrier)) =
          (bitstringWordEquiv Unit).symm (fun _ => d) := by
      have hrowDecomp : l1CoefficientMap a + d • allOnes ∈
          bk15CSSRows.rowCode.dual.dual.carrier := by
        rw [← had]
        exact hbits
      have hsubtype :
          (⟨bitstringWordEquiv (Fin 15) bits, hbits⟩ :
              bk15CSSRows.rowCode.dual.dual.carrier) =
            ⟨l1CoefficientMap a + d • allOnes, hrowDecomp⟩ :=
        Subtype.ext had
      calc
        _ = (bk15CSSRows.logicalBasisEquivLogicalQuotient
              bk15CSSRows_triorthogonal).symm
              (Submodule.Quotient.mk
                (⟨l1CoefficientMap a + d • allOnes, hrowDecomp⟩ :
                  bk15CSSRows.rowCode.dual.dual.carrier)) :=
            congrArg
              (fun value : bk15CSSRows.rowCode.dual.dual.carrier =>
                (bk15CSSRows.logicalBasisEquivLogicalQuotient
                  bk15CSSRows_triorthogonal).symm
                  (Submodule.Quotient.mk value)) hsubtype
        _ = _ := logicalLabel_l1_plus_allOnes_QECertNegativeAHistory a d hrowDecomp
    rw [bk15CSSRows.encoding_apply_of_mem_QECertNegativeAHistorySupport
      bk15CSSRows_triorthogonal logicalNegativeAState hbits,
      bk15CSSRows.encoding_apply_of_mem_QECertNegativeAHistorySupport
        bk15CSSRows_triorthogonal (logicalAErrorState c) hbits,
      hlabel, logicalAErrorState_label,
      zSupportPhase_eq_binaryPhaseScalar_wordPairing,
      had, l2_coset_pairing_l2dual_decomposition]
    ring
  · rw [bk15CSSRows.encoding_apply_of_not_mem_QECertNegativeAHistorySupport
      bk15CSSRows_triorthogonal logicalNegativeAState hbits,
      bk15CSSRows.encoding_apply_of_not_mem_QECertNegativeAHistorySupport
        bk15CSSRows_triorthogonal (logicalAErrorState c) hbits]
    simp

private theorem logicalRegisterToQubit_negativeA :
    logicalRegisterToQubit logicalNegativeAState =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) • aZeroState := by
  ext bit
  rw [logicalRegisterToQubit_apply]
  fin_cases bit
  · simp [logicalNegativeAState, aZeroState,
      OneQubitMagic.phaseState_apply_zero]
    ring
  · simp [logicalNegativeAState, aZeroState,
      OneQubitMagic.phaseState_apply_one]
    have hphase :
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (Real.pi / 4) = 1 := by
      rw [← OneQubitMagic.phaseAmplitude_add]
      convert OneQubitMagic.phaseAmplitude_zero using 1 <;> ring
    calc
      _ = (OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4)) *
          (Real.sqrt 2 : Complex)⁻¹ := by rw [hphase]; ring
      _ = _ := by ring

private theorem logicalRegisterToQubit_logicalAErrorState_zero :
    logicalRegisterToQubit (logicalAErrorState 0) =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) • aZeroState := by
  rw [show logicalAErrorState 0 = logicalNegativeAState by
    ext bits
    change binaryPhaseScalar ((0 : Bit) * (bitstringWordEquiv Unit bits) ()) *
      logicalNegativeAState bits = logicalNegativeAState bits
    rw [zero_mul, binaryPhaseScalar_zero, one_mul]]
  exact logicalRegisterToQubit_negativeA

private theorem logicalRegisterToQubit_logicalAErrorState_one :
    logicalRegisterToQubit (logicalAErrorState 1) =
      (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) • aOneState := by
  ext bit
  rw [logicalRegisterToQubit_apply]
  fin_cases bit
  · simp [logicalAErrorState, logicalNegativeAState, aOneState_eq_pauliZ,
      aZeroState, OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one, pauliZ_apply, zPhase]
    unfold binaryPhaseScalar
    split
    · rename_i h
      exact (one_ne_zero h).elim
    · ring
  · simp [logicalAErrorState, logicalNegativeAState, aOneState_eq_pauliZ,
      aZeroState, OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one, pauliZ_apply, zPhase]
    have hphase :
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
            OneQubitMagic.phaseAmplitude (Real.pi / 4) = 1 := by
      rw [← OneQubitMagic.phaseAmplitude_add]
      convert OneQubitMagic.phaseAmplitude_zero using 1 <;> ring
    calc
      _ = (OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          OneQubitMagic.phaseAmplitude (Real.pi / 4)) *
          (Real.sqrt 2 : Complex)⁻¹ := by
            unfold binaryPhaseScalar
            split
            · rw [hphase]
            · rename_i h
              exact (h rfl).elim
      _ = _ := by ring

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x bit
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)) x).ofLp bit =
    ((InnerProductSpace.rankOne Complex psi psi) x).ofLp bit
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply]
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi bit) =
        (z * star z) * inner Complex psi x * psi bit := by ring
    _ = inner Complex psi x * psi bit := by rw [hz]; ring

private theorem decoded_logicalAErrorState_rankOne (c : Bit) :
    (InnerProductSpace.rankOne Complex
      (logicalRegisterToQubit (logicalAErrorState c))
      (logicalRegisterToQubit (logicalAErrorState c))).toLinearMap =
      if c = 0 then
        (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
      else
        (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
  by_cases hzero : c = 0
  · rw [if_pos hzero, hzero, logicalRegisterToQubit_logicalAErrorState_zero]
    exact rankOne_global_phase
      (OneQubitMagic.phaseAmplitude (-Real.pi / 4)) aZeroState
      (OneQubitMagic.phaseAmplitude_mul_conj (-Real.pi / 4))
  · have hone : c = 1 := zmod_two_eq_one_of_ne_zero hzero
    rw [if_neg hzero, hone, logicalRegisterToQubit_logicalAErrorState_one]
    apply rankOne_global_phase
    calc
      (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) *
          star (-OneQubitMagic.phaseAmplitude (-Real.pi / 4)) =
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) *
          star (OneQubitMagic.phaseAmplitude (-Real.pi / 4)) := by
            rw [star_neg]
            ring
      _ = 1 := OneQubitMagic.phaseAmplitude_mul_conj (-Real.pi / 4)

private theorem rankOne_smul_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (scalar : Complex) (psi : H) :
    (InnerProductSpace.rankOne Complex (scalar • psi) (scalar • psi)).toLinearMap =
      (star scalar * scalar) •
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x
  simp [InnerProductSpace.rankOne_apply]
  rw [smul_smul]
  rw [mul_comm scalar (starRingEnd Complex scalar)]

private theorem decoderToQubitChannel_rankOne_encoded
    (psi : LogicalRegister) :
    decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (logicalRegisterToQubit psi) (logicalRegisterToQubit psi)).toLinearMap := by
  rw [decoderToQubitChannel, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, decoderChannel_rankOne_encoded_QECertNegativeAHistorySupport,
    QuditSubsystem.conjOperator_rankOne]

set_option maxHeartbeats 0 in
private theorem accepted_historyKraus_error_encoded
    (zOutcome : ZJointSyndrome) (error : Word)
    (hsyndrome : l1Syndrome error = 0) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) =
      (binaryPhaseScalar
          (l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ error) *
        (32 : Complex)⁻¹) •
        toHermitianQubitOperator (cssZCheck error)
          (ambientEncodingIsometry logicalNegativeAState) := by
  rw [accepted_historyKraus_error_QECertNegativeAHistory,
    historyKraus_ideal_QECertNegativeAHistory]
  simp only [hsyndrome, map_zero, signSyndrome, if_pos]
  rw [zeroZProjectedIdeal_zeroErrorWord_QECertNegativeAHistory, map_smul]
  rw [smul_smul]

set_option maxHeartbeats 0 in
private theorem accepted_historyKraus_error_zero
    (zOutcome : ZJointSyndrome) (error : Word)
    (hsyndrome : l1Syndrome error ≠ 0) :
    historyKraus
        (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
        (bk15ErrorWordState error) = 0 := by
  have hmatching : signSyndrome (l1Syndrome error) ≠
      signSyndrome (0 : XCheckIndex → Bit) := by
    intro hsign
    apply hsyndrome
    have hbinary := congrArg binarySyndrome hsign
    simpa using hbinary
  rw [accepted_historyKraus_error_QECertNegativeAHistory,
    historyKraus_ideal_QECertNegativeAHistory, if_neg hmatching]
  simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
private theorem decoded_accepted_history_rankOne_of_l1Dual
    (zOutcome : ZJointSyndrome) (error : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) (c : Bit)
    (herror : error = l2CoefficientMap b + c • allOnes) :
    decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap =
      (1024 : Complex)⁻¹ •
        (if c = 0 then
          (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
        else
          (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap) := by
  have hsyndrome : l1Syndrome error = 0 := by
    rw [herror]
    have hmember : l2CoefficientMap b + c • allOnes ∈ L1.dual.carrier := by
      rw [l1_dual_carrier_eq_model_QECertNegativeAHistorySupport]
      exact ⟨(b, c), rfl⟩
    rw [l1_dual_carrier_eq_l1Syndrome_ker_QECertNegativeAHistorySupport] at hmember
    exact hmember
  rw [accepted_historyKraus_error_encoded zOutcome error hsyndrome,
    herror, cssZCheck_l2_plus_allOnes_encoded,
    rankOne_smul_self, map_smul,
    decoderToQubitChannel_rankOne_encoded,
    decoded_logicalAErrorState_rankOne]
  generalize hphase : l2SyndromeSection (zBinarySyndrome zOutcome) ⬝ᵥ
    (l2CoefficientMap b + c • allOnes) = phase
  have hphaseStar : star (binaryPhaseScalar phase) = binaryPhaseScalar phase := by
    exact binaryPhaseScalar_star phase
  have hinv : star ((32 : Complex)⁻¹) = (32 : Complex)⁻¹ := by
    norm_num
  have hscalar :
      star (binaryPhaseScalar phase * (32 : Complex)⁻¹) *
        (binaryPhaseScalar phase * (32 : Complex)⁻¹) =
        (1024 : Complex)⁻¹ := by
    rw [star_mul, hphaseStar, hinv]
    calc
      ((32 : Complex)⁻¹ * binaryPhaseScalar phase) *
          (binaryPhaseScalar phase * (32 : Complex)⁻¹) =
        (binaryPhaseScalar phase * binaryPhaseScalar phase) *
          ((32 : Complex)⁻¹ * (32 : Complex)⁻¹) := by ring
      _ = (1024 : Complex)⁻¹ := by
        rw [binaryPhaseScalar_mul_self]
        norm_num
  rw [hscalar]

private theorem trace_negativeA_rankOne_aZero :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap)).re = 0 := by
  rw [OneQubitMagic.trace_mul_rankOne_QECertNegativeAHistorySupport]
  have hprojector : aBasisProjector .negative aZeroState = 0 := by
    simp [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      aBasisObservable_aZeroState]
  rw [hprojector]
  simp

private theorem trace_negativeA_rankOne_aOne :
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap)).re = 1 := by
  rw [OneQubitMagic.trace_mul_rankOne_QECertNegativeAHistorySupport]
  have hprojector : aBasisProjector .negative aOneState = aOneState := by
    simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      aBasisObservable_aOneState]
    module
  rw [hprojector, inner_self_eq_norm_sq_to_K, aOneState_norm]
  norm_num

set_option maxRecDepth 262144 in
private theorem mem_l1DualWords_iff_exists_l2_plus_allOnes
    (error : Word) :
    error ∈ l1DualWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, ∃ c : Bit,
        error = l2CoefficientMap b + c • allOnes := by
  rw [mem_l1DualWords_iff_QECertNegativeAHistorySupport, mem_l1_dual_iff_exists_l2_plus_allOnes_QECertNegativeAHistorySupport]

set_option maxRecDepth 262144 in
private theorem l2LogicalCosetWords_subset_l1DualWords
    {error : Word} (herror : error ∈ l2LogicalCosetWords) :
    error ∈ l1DualWords := by
  rw [mem_l2LogicalCosetWords_iff_QECertNegativeAHistorySupport] at herror
  rcases herror with ⟨b, rfl⟩
  rw [mem_l1DualWords_iff_exists_l2_plus_allOnes]
  exact ⟨b, 1, by simp⟩

set_option maxRecDepth 262144 in
private theorem negativeA_trace_decoded_accepted_history
    (zOutcome : ZJointSyndrome) (error : Word) :
    (negativeADecodedTrace
      (InnerProductSpace.rankOne Complex
        (historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState error))
        (historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState error))).toLinearMap).re =
      if error ∈ l2LogicalCosetWords then (1024 : Real)⁻¹ else 0 := by
  classical
  by_cases haccepted : error ∈ l1DualWords
  · obtain ⟨b, c, herror⟩ :=
      (mem_l1DualWords_iff_exists_l2_plus_allOnes error).mp haccepted
    unfold negativeADecodedTrace
    change (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative * decoderToQubitChannel
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap)).re = _
    rw [decoded_accepted_history_rankOne_of_l1Dual zOutcome error b c herror]
    by_cases hzero : c = 0
    · have hnotlogical : error ∉ l2LogicalCosetWords := by
        intro hlogical
        have hinL2 : error ∈ l2Words := by
          rw [l2Words, Finset.mem_image]
          exact ⟨b, Finset.mem_univ _, by simpa [hzero] using herror.symm⟩
        exact Finset.disjoint_left.mp l2Words_disjoint_l2LogicalCosetWords_QECertNegativeAHistorySupport
          hinL2 hlogical
      rw [if_neg hnotlogical, if_pos hzero, mul_smul_comm, map_smul]
      simp only [smul_eq_mul, Complex.mul_re]
      rw [trace_negativeA_rankOne_aZero]
      norm_num
    · have hone : c = 1 := zmod_two_eq_one_of_ne_zero hzero
      have hlogical : error ∈ l2LogicalCosetWords := by
        rw [mem_l2LogicalCosetWords_iff_QECertNegativeAHistorySupport]
        exact ⟨b, by simpa [hone] using herror⟩
      rw [if_pos hlogical, if_neg hzero, mul_smul_comm, map_smul]
      simp only [smul_eq_mul, Complex.mul_re]
      rw [trace_negativeA_rankOne_aOne]
      norm_num
  · have hsyndrome : l1Syndrome error ≠ 0 := by
      intro hzero
      apply haccepted
      rw [mem_l1DualWords_iff_QECertNegativeAHistorySupport, l1_dual_carrier_eq_l1Syndrome_ker_QECertNegativeAHistorySupport]
      exact hzero
    have hnotlogical : error ∉ l2LogicalCosetWords := by
      intro hlogical
      exact haccepted (l2LogicalCosetWords_subset_l1DualWords hlogical)
    rw [accepted_historyKraus_error_zero zOutcome error hsyndrome,
      if_neg hnotlogical]
    have hrankZero :
        (InnerProductSpace.rankOne Complex (0 : BK15Register)
          (0 : BK15Register)).toLinearMap = (0 : Operator BK15Register) := by
      have hrankZeroCL :
          InnerProductSpace.rankOne Complex (0 : BK15Register) (0 : BK15Register) = 0 := by
        rw [InnerProductSpace.rankOne_eq_zero]
        exact Or.inl rfl
      rw [hrankZeroCL]
      rfl
    rw [hrankZero]
    have htraceZero : negativeADecodedTrace (0 : Operator BK15Register) = (0 : Complex) :=
      negativeADecodedTrace.map_zero
    rw [htraceZero]
    rfl

set_option maxRecDepth 262144 in
private theorem zJointSyndrome_card : Fintype.card ZJointSyndrome = 1024 := by
  have hstabilizer : Fintype.card StabilizerOutcome = 2 := by decide +kernel
  change Fintype.card StabilizerOutcome ^ (4 + Fintype.card QuadraticIndex) = 1024
  rw [hstabilizer, quadraticIndex_card_QECertNegativeAHistorySupport]
  norm_num

theorem sum_negativeA_trace_decoded_accepted_history_QECert
    (error : Word) :
    ∑ zOutcome : ZJointSyndrome,
      (negativeADecodedTrace
        (InnerProductSpace.rankOne Complex
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))
          (historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState error))).toLinearMap).re =
      if error ∈ l2LogicalCosetWords then 1 else 0 := by
  classical
  simp_rw [negativeA_trace_decoded_accepted_history]
  by_cases hlogical : error ∈ l2LogicalCosetWords
  · simp only [if_pos hlogical, Finset.sum_const, Finset.card_univ]
    rw [zJointSyndrome_card]
    norm_num
  · simp [hlogical]

end Recurrence
end BK15
end Distillation
end QEC
end
end


