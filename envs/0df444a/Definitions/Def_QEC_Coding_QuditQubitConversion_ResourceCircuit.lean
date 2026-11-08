-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
-- name    : QEC_Coding_QuditQubitConversion_ResourceCircuit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:07:31.927839+00:00
-- url     : https://prove2.me/theorems/1385938a-59e1-4445-9e7e-1ceb7a0f4156
-- title:
--   Resource Circuit
-- statement:
--   Definitions and structural lemmas for Resource Circuit, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/ResourceCircuit.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_label_symm
import Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_symm_apply
import Theorems.Thm_QEC_Coding_f1024_card
import Theorems.Thm_QEC_Coding_why24AppendixReverseCorrectionPhase_add_source
import Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_trace
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
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
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
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
namespace QEC.Coding
noncomputable def why24UniformAmplitude : Complex :=
  (Real.sqrt (Fintype.card F1024 : Real) : Complex)⁻¹
theorem why24UniformAmplitude_identity :
    starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
        (Fintype.card F1024 : Complex) = 1 := by
  have hcard : 0 < Fintype.card F1024 := Fintype.card_pos
  have hsqrtPos : 0 < Real.sqrt (Fintype.card F1024 : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) *
          (Real.sqrt (Fintype.card F1024 : Real) : Complex) =
        (Fintype.card F1024 : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Fintype.card F1024)
  simp only [why24UniformAmplitude, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Fintype.card F1024 : Real) : Complex) =
        (Real.sqrt (Fintype.card F1024 : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]
noncomputable def why24QuditPlusState : Why24QuditSpace :=
  WithLp.toLp 2 fun _ => why24UniformAmplitude
@[simp] theorem why24QuditPlusState_apply (β : F1024) :
    why24QuditPlusState β = why24UniformAmplitude :=
  rfl
noncomputable def why24QubitPlusState : Why24QubitSpace :=
  why24QuditQubitUnitary why24QuditPlusState
noncomputable def why24UOneSevenQuditResource : Why24QuditSpace :=
  why24UOneSeven why24QuditPlusState
noncomputable def why24UOneSevenQubitResource : Why24QubitSpace :=
  why24QubitUOneSeven why24QubitPlusState
theorem why24UOneSevenQubitResource_eq_apply :
    why24UOneSevenQubitResource = why24QubitUOneSeven why24QubitPlusState :=
  rfl
def why24AppendixGatePhase (gate : Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : ZMod 2 :=
  let word := PauliSymplectic.bitstringWordEquiv (Fin 10) bits
  match gate with
  | .z site => word site
  | .cz left right => word left * word right
  | .ccz first second third => word first * word second * word third
noncomputable def why24AppendixGateOperator (gate : Why24AppendixGate) :
    Semantics.Operator Why24QubitSpace where
  toFun ψ := WithLp.toLp 2 fun bits =>
    PauliSymplectic.binaryPhaseScalar (why24AppendixGatePhase gate bits) * ψ bits
  map_add' ψ φ := by
    ext bits
    simp [mul_add]
  map_smul' c ψ := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]
theorem why24AppendixGateOperator_apply (gate : Why24AppendixGate)
    (ψ : Why24QubitSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixGateOperator gate ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixGatePhase gate bits) * ψ bits :=
  rfl
def why24AppendixPhaseList (gates : List Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) : ZMod 2 :=
  gates.foldr (fun gate phase => why24AppendixGatePhase gate bits + phase) 0
noncomputable def why24AppendixCircuitOf (gates : List Why24AppendixGate) :
    Semantics.Operator Why24QubitSpace :=
  gates.foldr (fun gate circuit => why24AppendixGateOperator gate * circuit) 1
theorem why24AppendixCircuitOf_apply (gates : List Why24AppendixGate)
    (ψ : Why24QubitSpace) (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixCircuitOf gates ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixPhaseList gates bits) * ψ bits := by
  unfold why24AppendixCircuitOf
  induction gates with
  | nil => simp [why24AppendixPhaseList]
  | cons gate gates ih =>
      simp only [List.foldr_cons, Module.End.mul_apply, why24AppendixGateOperator_apply, ih,
        why24AppendixPhaseList]
      rw [← mul_assoc, ← PauliSymplectic.binaryPhaseScalar_add]
noncomputable def why24AppendixCircuit : Semantics.Operator Why24QubitSpace :=
  why24AppendixCircuitOf why24AppendixGateList
theorem why24AppendixCircuit_apply_phase (ψ : Why24QubitSpace)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixCircuit ψ bits =
      PauliSymplectic.binaryPhaseScalar (why24AppendixPhaseList why24AppendixGateList bits) *
        ψ bits := by
  change why24AppendixCircuitOf why24AppendixGateList ψ bits =
    PauliSymplectic.binaryPhaseScalar
      (why24AppendixPhaseList why24AppendixGateList bits) * ψ bits
  exact why24AppendixCircuitOf_apply why24AppendixGateList ψ bits
theorem why24AppendixGatePhase_eq_word (gate : Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixGatePhase gate bits =
      why24AppendixWordGatePhase gate
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) :=
  rfl
theorem why24AppendixPhaseList_eq_word (gates : List Why24AppendixGate)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24AppendixPhaseList gates bits =
      why24AppendixWordPhaseList gates
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      simp only [why24AppendixPhaseList, why24AppendixWordPhaseList,
        List.foldr_cons, why24AppendixGatePhase_eq_word, ih]
theorem why24Trace_label_symm_eq_phaseList
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    Algebra.trace (ZMod 2) F1024
        ((why24ComputationalLabelEquiv.symm bits) ^ 7) =
      why24AppendixWordPhaseList why24AppendixGateList
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
  have hlabel : why24ComputationalLabelEquiv.symm bits =
      f1024SelectedCoordinates.symm
        (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
    calc
      why24ComputationalLabelEquiv.symm bits =
          f1024SelectedCoordinates.symm
            (f1024SelectedCoordinates
              (why24ComputationalLabelEquiv.symm bits)) := by
                rw [f1024SelectedCoordinates_symm_apply]
      _ = f1024SelectedCoordinates.symm
          (PauliSymplectic.bitstringWordEquiv (Fin 10) bits) := by
            rw [f1024SelectedCoordinates_label_symm]
  rw [hlabel]
  exact (why24AppendixWordPhaseList_eq_trace
    (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)).symm
theorem why24AppendixCircuit_apply_eq_why24QubitUOneSeven
    (ψ : Why24QubitSpace) :
    why24AppendixCircuit ψ = why24QubitUOneSeven ψ := by
  ext bits
  rw [why24AppendixCircuit_apply_phase, why24AppendixPhaseList_eq_word,
    ← why24Trace_label_symm_eq_phaseList]
  rw [why24QubitUOneSeven, Semantics.UnitaryTransport.conjOperator_apply]
  change
    PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24ComputationalLabelEquiv.symm bits) ^ 7)) * ψ bits =
      why24QuditQubitBasisIsometry
        (why24UOneSeven (why24QuditQubitBasisIsometry.symm ψ)) bits
  rw [why24QuditQubitBasisIsometry_apply, why24U_apply,
    why24QuditQubitBasisIsometry_symm_apply]
  simp only [Equiv.apply_symm_apply, one_mul]
theorem why24AppendixForwardPreparation :
    why24AppendixCircuit why24QubitPlusState =
      why24UOneSevenQubitResource := by
  rw [why24UOneSevenQubitResource_eq_apply,
    why24AppendixCircuit_apply_eq_why24QubitUOneSeven]
theorem why24QubitPlusState_apply
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24QubitPlusState bits = why24UniformAmplitude := by
  change why24QuditPlusState (why24ComputationalLabelEquiv.symm bits) =
    why24UniformAmplitude
  exact why24QuditPlusState_apply _
theorem why24UOneSevenQubitResource_apply
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24UOneSevenQubitResource bits =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixWordPhaseList why24AppendixGateList
            (PauliSymplectic.bitstringWordEquiv (Fin 10) bits)) *
        why24UniformAmplitude := by
  rw [← why24AppendixForwardPreparation,
    why24AppendixCircuit_apply_phase, why24AppendixPhaseList_eq_word,
    why24QubitPlusState_apply]
noncomputable def why24AppendixReverseRawBranch
    (outcome : Why24AppendixReverseOutcome) : Why24CCZSpace :=
  WithLp.toLp 2 fun retained =>
    why24UOneSevenQubitResource
      (why24AppendixReverseRecombine retained outcome)
theorem why24AppendixReverseRawBranch_apply
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseRawBranch outcome retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseSourcePhase outcome retained) *
        why24UniformAmplitude := by
  rw [why24AppendixReverseRawBranch,
    why24UOneSevenQubitResource_apply]
  rfl
noncomputable def why24AppendixReverseCorrection
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.Operator Why24CCZSpace where
  toFun psi := WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar
        (why24AppendixReverseCorrectionPhase outcome retained) *
      psi retained
  map_add' left right := by
    ext retained
    simp [mul_add]
  map_smul' scalar psi := by
    ext retained
    simp [smul_eq_mul, mul_left_comm]
theorem why24AppendixReverseCorrection_apply
    (outcome : Why24AppendixReverseOutcome) (psi : Why24CCZSpace)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseCorrection outcome psi retained =
      PauliSymplectic.binaryPhaseScalar
          (why24AppendixReverseCorrectionPhase outcome retained) *
        psi retained :=
  rfl
theorem why24BinaryPhaseScalar_mul_self (phase : ZMod 2) :
    PauliSymplectic.binaryPhaseScalar phase *
        PauliSymplectic.binaryPhaseScalar phase = 1 := by
  rw [← PauliSymplectic.binaryPhaseScalar_add,
    CharTwo.add_self_eq_zero,
    PauliSymplectic.binaryPhaseScalar_zero]
noncomputable def why24PhaseUniformRetainedBranch
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    Why24CCZSpace :=
  WithLp.toLp 2 fun retained =>
    PauliSymplectic.binaryPhaseScalar (phase retained) *
      why24UniformAmplitude
theorem why24PhaseUniformRetainedBranch_apply
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24PhaseUniformRetainedBranch phase retained =
      PauliSymplectic.binaryPhaseScalar (phase retained) *
        why24UniformAmplitude :=
  rfl
theorem why24PhaseUniformRetainedBranch_inner_self
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    inner Complex (why24PhaseUniformRetainedBranch phase)
        (why24PhaseUniformRetainedBranch phase) = (1 / 128 : Complex) := by
  rw [PiLp.inner_apply]
  calc
    (∑ retained : Semantics.Qubit.Bitstring (Fin 3),
      inner Complex
        (why24PhaseUniformRetainedBranch phase retained)
        (why24PhaseUniformRetainedBranch phase retained)) =
        ∑ _retained : Semantics.Qubit.Bitstring (Fin 3),
          why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude := by
      apply Finset.sum_congr rfl
      intro retained _
      rw [why24PhaseUniformRetainedBranch_apply]
      simp only [RCLike.inner_apply, map_mul]
      have hstar :
          starRingEnd Complex
              (PauliSymplectic.binaryPhaseScalar (phase retained)) =
            PauliSymplectic.binaryPhaseScalar (phase retained) :=
        PauliSymplectic.binaryPhaseScalar_star _
      rw [hstar]
      calc
        (PauliSymplectic.binaryPhaseScalar (phase retained) *
            why24UniformAmplitude) *
            (PauliSymplectic.binaryPhaseScalar (phase retained) *
              starRingEnd Complex why24UniformAmplitude) =
            (PauliSymplectic.binaryPhaseScalar (phase retained) *
              PauliSymplectic.binaryPhaseScalar (phase retained)) *
                (why24UniformAmplitude *
                  starRingEnd Complex why24UniformAmplitude) := by ring
        _ = why24UniformAmplitude *
            starRingEnd Complex why24UniformAmplitude := by
              rw [why24BinaryPhaseScalar_mul_self, one_mul]
    _ = (1 / 128 : Complex) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard :
          Fintype.card (Semantics.Qubit.Bitstring (Fin 3)) = 8 := by
        rw [Semantics.Qubit.card_bitstring]
        norm_num
      rw [Finset.card_univ, hcard]
      change (8 : Complex) *
          (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
        (1 / 128 : Complex)
      have huniform :
          starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
              (1024 : Complex) = 1 := by
        simpa only [f1024_card, Nat.cast_ofNat] using
          why24UniformAmplitude_identity
      calc
        (8 : Complex) *
            (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
            (starRingEnd Complex why24UniformAmplitude *
              why24UniformAmplitude * (1024 : Complex)) / 128 := by ring
        _ = (1 / 128 : Complex) := by rw [huniform]
theorem why24PhaseUniformRetainedBranch_normSq
    (phase : Semantics.Qubit.Bitstring (Fin 3) → ZMod 2) :
    ‖why24PhaseUniformRetainedBranch phase‖ ^ 2 = (1 / 128 : Real) := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    why24PhaseUniformRetainedBranch_inner_self]
  norm_num
noncomputable def why24AppendixReverseBornWeight
    (outcome : Why24AppendixReverseOutcome) : Real :=
  ‖why24AppendixReverseRawBranch outcome‖ ^ 2
theorem why24AppendixReverseCorrectedRawBranch_eq_phaseUniform
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseCorrection outcome
        (why24AppendixReverseRawBranch outcome) =
      why24PhaseUniformRetainedBranch why24CCZPhase := by
  ext retained
  rw [why24AppendixReverseCorrection_apply,
    why24AppendixReverseRawBranch_apply,
    why24PhaseUniformRetainedBranch_apply,
    ← mul_assoc,
    ← PauliSymplectic.binaryPhaseScalar_add,
    why24AppendixReverseCorrectionPhase_add_source]
noncomputable def why24CCZMagicState : Why24CCZSpace :=
  (Real.sqrt 128 : Complex) •
    why24PhaseUniformRetainedBranch why24CCZPhase
theorem why24CCZMagicState_norm : ‖why24CCZMagicState‖ = 1 := by
  rw [why24CCZMagicState, norm_smul]
  have hsqrtNorm : ‖(Real.sqrt 128 : Complex)‖ = Real.sqrt 128 := by
    simp
  rw [hsqrtNorm]
  have hsqrtSq : (Real.sqrt 128) ^ 2 = (128 : Real) := by
    exact Real.sq_sqrt (by norm_num)
  have hbranch :=
    why24PhaseUniformRetainedBranch_normSq why24CCZPhase
  have hproductSq :
      (Real.sqrt 128 *
        ‖why24PhaseUniformRetainedBranch why24CCZPhase‖) ^ 2 = 1 := by
    rw [mul_pow, hsqrtSq, hbranch]
    norm_num
  have hproductNonneg : 0 ≤ Real.sqrt 128 *
      ‖why24PhaseUniformRetainedBranch why24CCZPhase‖ :=
    mul_nonneg (Real.sqrt_nonneg 128)
      (norm_nonneg (why24PhaseUniformRetainedBranch why24CCZPhase))
  nlinarith
theorem why24CCZMagicState_normSq :
    ‖why24CCZMagicState‖ ^ 2 = 1 := by
  rw [why24CCZMagicState_norm]
  norm_num
noncomputable def why24CCZMagicStateDensity :
    Semantics.DensityOperator Why24CCZSpace :=
  Semantics.DensityOperator.pureDensity
    why24CCZMagicState why24CCZMagicState_normSq
noncomputable def why24AppendixReverseNormalizedBranch
    (outcome : Why24AppendixReverseOutcome) : Why24CCZSpace :=
  (Real.sqrt 128 : Complex) •
    why24AppendixReverseCorrection outcome
      (why24AppendixReverseRawBranch outcome)
theorem why24AppendixReverseNormalizedBranch_eq_ccz
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseNormalizedBranch outcome =
      why24CCZMagicState := by
  rw [why24AppendixReverseNormalizedBranch,
    why24AppendixReverseCorrectedRawBranch_eq_phaseUniform,
    why24CCZMagicState]
theorem why24AppendixReverseNormalizedBranch_normSq
    (outcome : Why24AppendixReverseOutcome) :
    ‖why24AppendixReverseNormalizedBranch outcome‖ ^ 2 = 1 := by
  rw [why24AppendixReverseNormalizedBranch_eq_ccz,
    why24CCZMagicState_normSq]
noncomputable def why24AppendixReverseConditional
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.DensityOperator Why24CCZSpace :=
  Semantics.DensityOperator.pureDensity
    (why24AppendixReverseNormalizedBranch outcome)
    (why24AppendixReverseNormalizedBranch_normSq outcome)
end QEC.Coding


