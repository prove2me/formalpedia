-- Prove2me | Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryAction_QECert
-- name    : QEC_Distillation_BK15_NegativeAHistoryAction_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T20:19:36.86526+00:00
-- url     : https://prove2.me/theorems/edfa5632-dcc2-4097-9b9c-93eafe880bd0
-- title:
--   BK15 negative-A history action
-- statement:
--   Exact action identities used in the BK15 negative-A history sum.
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
theorem zeroZProjectedIdeal_zeroErrorWord_QECertNegativeAHistory :
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
theorem historyKraus_ideal_QECertNegativeAHistory (history : History) :
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
theorem accepted_historyKraus_error_QECertNegativeAHistory (zOutcome : ZJointSyndrome)
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


