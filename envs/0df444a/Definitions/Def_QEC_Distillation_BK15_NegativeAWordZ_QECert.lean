-- Prove2me | Definitions.Def_QEC_Distillation_BK15_NegativeAWordZ_QECert
-- name    : QEC_Distillation_BK15_NegativeAWordZ_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T00:12:40.398805+00:00
-- url     : https://prove2.me/theorems/9df6d2a4-c96d-4d17-99ed-98dd84845ac3
-- title:
--   BK15 negative-A word sum over Z syndromes
-- statement:
--   An exact expression for the accepted negative-A weight in the BK15 distillation protocol, using word and Z-syndrome sums.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
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

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct

private theorem historyOutcome_accepted_iff
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome) :
    historyOutcome (zOutcome, xOutcome) = .accepted ↔
      xOutcome = signSyndrome (0 : XCheckIndex → Bit) := by
  constructor
  · intro haccepted
    change (if binarySyndrome xOutcome = 0 then DistillationOutcome.accepted
      else DistillationOutcome.rejected) = DistillationOutcome.accepted at haccepted
    by_cases hzero : binarySyndrome xOutcome = 0
    ·
      calc
        xOutcome = signSyndrome (binarySyndrome xOutcome) :=
          (signSyndrome_binarySyndrome xOutcome).symm
        _ = signSyndrome 0 := by rw [hzero]
    · simp [hzero] at haccepted
  · intro hzero
    subst xOutcome
    simp [historyOutcome, binarySyndrome_signSyndrome]

private theorem comp_sum {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : K →ₗ[Complex] L) (B : index → H →ₗ[Complex] K) :
    A.comp (∑ i, B i) = ∑ i, A.comp (B i) := by
  ext x
  simp

private theorem sum_comp {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : index → K →ₗ[Complex] L) (B : H →ₗ[Complex] K) :
    (∑ i, A i).comp B = ∑ i, (A i).comp B := by
  ext x
  simp

private theorem sandwich_rankOne {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]

private theorem acceptedNegativeAWeight_eq_history_word_sum
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ history : History,
        (if historyOutcome history = .accepted then
          ∑ word : Word, bk15WordWeight epsilon word *
            (negativeADecodedTrace
              (InnerProductSpace.rankOne Complex
                (historyKraus history (bk15ErrorWordState word))
                (historyKraus history (bk15ErrorWordState word))).toLinearMap).re
        else 0) := by
  classical
  unfold acceptedNegativeAWeight
  rw [rawEndpoint_eq_branchOperator,
    FiniteInstrument.branchOperator_apply, rawInput_toOperator_sum]
  simp only [historyInstrument, historyKrausFamily]
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hvisible : historyOutcome history = .accepted
  · erw [if_pos hvisible, if_pos hvisible]
    rw [sum_comp, comp_sum, map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [LinearMap.smul_comp, LinearMap.comp_smul,
      sandwich_rankOne, map_smul]
    simp [Complex.mul_re]
  · erw [if_neg hvisible, if_neg hvisible]
    simp

theorem acceptedNegativeAWeight_eq_word_z_sum_QECert
    (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      ∑ word : Word, bk15WordWeight epsilon word *
        ∑ zOutcome : ZJointSyndrome,
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
  classical
  rw [acceptedNegativeAWeight_eq_history_word_sum, Fintype.sum_prod_type]
  calc
    ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (if historyOutcome (zOutcome, xOutcome) = .accepted then
          ∑ word : Word, bk15WordWeight epsilon word *
            (negativeADecodedTrace
              (InnerProductSpace.rankOne Complex
                (historyKraus (zOutcome, xOutcome)
                  (bk15ErrorWordState word))
                (historyKraus (zOutcome, xOutcome)
                  (bk15ErrorWordState word))).toLinearMap).re
        else 0) =
      ∑ zOutcome : ZJointSyndrome, ∑ word : Word,
        bk15WordWeight epsilon word *
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
          apply Finset.sum_congr rfl
          intro zOutcome _
          rw [Fintype.sum_eq_single
            (signSyndrome (0 : XCheckIndex → Bit))]
          · simp [historyOutcome_accepted_iff]
          · intro xOutcome hxOutcome
            have hnotaccepted :
              historyOutcome (zOutcome, xOutcome) ≠ .accepted := by
                intro haccepted
                exact hxOutcome (historyOutcome_accepted_iff zOutcome xOutcome |>.mp
                  haccepted)
            simp [hnotaccepted]
    _ = ∑ word : Word, bk15WordWeight epsilon word *
        ∑ zOutcome : ZJointSyndrome,
          (negativeADecodedTrace
            (InnerProductSpace.rankOne Complex
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))
              (historyKraus
                (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
                (bk15ErrorWordState word))).toLinearMap).re := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro word _
          rw [← Finset.mul_sum]

end Recurrence
end BK15
end Distillation
end QEC


