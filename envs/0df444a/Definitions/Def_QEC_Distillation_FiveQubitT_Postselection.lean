-- Prove2me | Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
-- name    : QEC_Distillation_FiveQubitT_Postselection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T18:57:42.932406+00:00
-- url     : https://prove2.me/theorems/ac7df10d-b873-447a-a4c0-d2193dad5d6e
-- title:
--   Postselection
-- statement:
--   Definitions and structural lemmas for Postselection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection_Part1_QECert
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator
import Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator_eq_blochProjector
import Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_zero
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_tMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_tMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_le_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tProjector_isSymmetricProjection
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_smul_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_zSupportPhase_flipSupport
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
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
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct
noncomputable def fiveQubitPreparedMatrixRow
    (epsilon : Real) (input : Fin 2) (left : FiveBitTuple) : Complex :=
  ∑ right : FiveBitTuple,
    tDiagonalMatrixEntry epsilon left.1 right.1 *
      (tDiagonalMatrixEntry epsilon left.2.1 right.2.1 *
        (tDiagonalMatrixEntry epsilon left.2.2.1 right.2.2.1 *
          (tDiagonalMatrixEntry epsilon left.2.2.2.1 right.2.2.2.1 *
            (tDiagonalMatrixEntry epsilon left.2.2.2.2 right.2.2.2.2 *
              fiveQubitLogicalAmplitude input right))))
def fiveQubitMatrixEntryScalar (d : Complex) : Fin 2 → Fin 2 → Complex
  | 0, 0 => (1 + d) / 2
  | 0, 1 => d * (1 - Complex.I) / 2
  | 1, 0 => d * (1 + Complex.I) / 2
  | 1, 1 => (1 - d) / 2
noncomputable def fiveQubitPreparedRowScalar
    (d : Complex) (input : Fin 2) (left : FiveBitTuple) : Complex :=
  ∑ right : FiveBitTuple,
    fiveQubitMatrixEntryScalar d left.1 right.1 *
      (fiveQubitMatrixEntryScalar d left.2.1 right.2.1 *
        (fiveQubitMatrixEntryScalar d left.2.2.1 right.2.2.1 *
          (fiveQubitMatrixEntryScalar d left.2.2.2.1 right.2.2.2.1 *
            (fiveQubitMatrixEntryScalar d left.2.2.2.2 right.2.2.2.2 *
              fiveQubitLogicalAmplitude input right))))
theorem fiveQubitPreparedMatrixRow_eq_scalar
    (epsilon : Real) (input : Fin 2) (left : FiveBitTuple) :
    fiveQubitPreparedMatrixRow epsilon input left =
      fiveQubitPreparedRowScalar (((1 - 2 * epsilon) * (Real.sqrt 3)⁻¹ : Real) : Complex)
        input left := by
  rfl
attribute [local irreducible] fiveQubitPreparedRowScalar
def arrayAmplitudeZero : FiveBitTuple → GaussianInt
  | (0, 0, 0, 0, 0) => 1
  | (0, 0, 0, 1, 1) => -1
  | (0, 0, 1, 0, 1) => 1
  | (0, 0, 1, 1, 0) => -1
  | (0, 1, 0, 0, 1) => 1
  | (0, 1, 0, 1, 0) => 1
  | (0, 1, 1, 0, 0) => -1
  | (0, 1, 1, 1, 1) => -1
  | (1, 0, 0, 0, 1) => -1
  | (1, 0, 0, 1, 0) => 1
  | (1, 0, 1, 0, 0) => 1
  | (1, 0, 1, 1, 1) => -1
  | (1, 1, 0, 0, 0) => -1
  | (1, 1, 0, 1, 1) => -1
  | (1, 1, 1, 0, 1) => -1
  | (1, 1, 1, 1, 0) => -1
  | _ => 0
def arrayEntry : Fin 2 → Fin 2 → GaussianInt × GaussianInt
  | 0, 0 => (1, 1)
  | 0, 1 => (0, 1 - (⟨0, 1⟩ : GaussianInt))
  | 1, 0 => (0, 1 + (⟨0, 1⟩ : GaussianInt))
  | 1, 1 => (1, -1)
def arrayConstant (c : GaussianInt) (k : Fin 6) : GaussianInt :=
  if k.val = 0 then c else 0
def arrayMulLinear (ab : GaussianInt × GaussianInt)
    (p : Fin 6 → GaussianInt) (k : Fin 6) : GaussianInt :=
  ab.1 * p k + if k.val = 0 then 0 else
    ab.2 * p ⟨k.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le k.val 1) k.isLt⟩
attribute [local irreducible] GaussianInt.toComplex
noncomputable def arrayEval (p : Fin 6 → GaussianInt) (d : Complex) : Complex :=
  ∑ k : Fin 6, GaussianInt.toComplex (p k) * d ^ k.val
theorem arrayEval_five_linear
    (d : Complex) (c : GaussianInt)
    (ab0 ab1 ab2 ab3 ab4 : GaussianInt × GaussianInt) :
    arrayEval (arrayMulLinear ab0 (arrayMulLinear ab1
      (arrayMulLinear ab2 (arrayMulLinear ab3
        (arrayMulLinear ab4 (arrayConstant c)))))) d =
      (GaussianInt.toComplex ab0.1 + GaussianInt.toComplex ab0.2 * d) *
      (GaussianInt.toComplex ab1.1 + GaussianInt.toComplex ab1.2 * d) *
      (GaussianInt.toComplex ab2.1 + GaussianInt.toComplex ab2.2 * d) *
      (GaussianInt.toComplex ab3.1 + GaussianInt.toComplex ab3.2 * d) *
      (GaussianInt.toComplex ab4.1 + GaussianInt.toComplex ab4.2 * d) *
      GaussianInt.toComplex c := by
  simp [arrayEval, Fin.sum_univ_succ, arrayMulLinear, arrayConstant,
    map_add, map_mul]
  ring
theorem arrayEntry_complex (d : Complex) (output input : Fin 2) :
    (GaussianInt.toComplex (arrayEntry output input).1 +
      GaussianInt.toComplex (arrayEntry output input).2 * d) / 2 =
        fiveQubitMatrixEntryScalar d output input := by
  fin_cases output <;> fin_cases input <;>
    norm_num [arrayEntry, fiveQubitMatrixEntryScalar, GaussianInt.toComplex_def] <;> ring
theorem arrayAmplitudeZero_complex (right : FiveBitTuple) :
    GaussianInt.toComplex (arrayAmplitudeZero right) / 4 =
      fiveQubitLogicalAmplitude 0 right := by
  rcases right with ⟨r0, r1, r2, r3, r4⟩
  fin_cases r0 <;> fin_cases r1 <;> fin_cases r2 <;>
    fin_cases r3 <;> fin_cases r4 <;>
    norm_num [arrayAmplitudeZero, fiveQubitLogicalAmplitude,
      fiveQubitLogicalZeroAmplitude, GaussianInt.toComplex_def]
def arrayAmplitudeOne : FiveBitTuple → GaussianInt
  | (0, 0, 0, 0, 1) => -1
  | (0, 0, 0, 1, 0) => -1
  | (0, 0, 1, 0, 0) => -1
  | (0, 0, 1, 1, 1) => -1
  | (0, 1, 0, 0, 0) => -1
  | (0, 1, 0, 1, 1) => 1
  | (0, 1, 1, 0, 1) => 1
  | (0, 1, 1, 1, 0) => -1
  | (1, 0, 0, 0, 0) => -1
  | (1, 0, 0, 1, 1) => -1
  | (1, 0, 1, 0, 1) => 1
  | (1, 0, 1, 1, 0) => 1
  | (1, 1, 0, 0, 1) => -1
  | (1, 1, 0, 1, 0) => 1
  | (1, 1, 1, 0, 0) => -1
  | (1, 1, 1, 1, 1) => 1
  | _ => 0
def arrayAmplitude : Fin 2 → FiveBitTuple → GaussianInt
  | 0 => arrayAmplitudeZero
  | 1 => arrayAmplitudeOne
def arrayProductFor (input : Fin 2) (left right : FiveBitTuple) : Fin 6 → GaussianInt :=
  arrayMulLinear (arrayEntry left.1 right.1)
    (arrayMulLinear (arrayEntry left.2.1 right.2.1)
      (arrayMulLinear (arrayEntry left.2.2.1 right.2.2.1)
        (arrayMulLinear (arrayEntry left.2.2.2.1 right.2.2.2.1)
          (arrayMulLinear (arrayEntry left.2.2.2.2 right.2.2.2.2)
            (arrayConstant (arrayAmplitude input right))))))
def arrayRowFor (input : Fin 2) (left : FiveBitTuple) (k : Fin 6) : GaussianInt :=
  ∑ right : FiveBitTuple, arrayProductFor input left right k
def arrayTarget : Fin 2 → FiveBitTuple → Fin 6 → GaussianInt
  | 0, (0, 0, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨5, 0⟩
    | 2 => ⟨10, 0⟩
    | 3 => ⟨10, 0⟩
    | 4 => ⟨25, 0⟩
    | 5 => ⟨21, 0⟩
    | _ => 0
  | 0, (0, 0, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, 1⟩
    | 2 => ⟨4, 4⟩
    | 3 => ⟨14, 14⟩
    | 4 => ⟨4, 4⟩
    | 5 => ⟨-3, -3⟩
    | _ => 0
  | 0, (0, 0, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, 1⟩
    | 2 => ⟨4, 4⟩
    | 3 => ⟨14, 14⟩
    | 4 => ⟨4, 4⟩
    | 5 => ⟨-3, -3⟩
    | _ => 0
  | 0, (0, 0, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨6, 8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨-9, 8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 0, (0, 0, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, 1⟩
    | 2 => ⟨4, 4⟩
    | 3 => ⟨14, 14⟩
    | 4 => ⟨4, 4⟩
    | 5 => ⟨-3, -3⟩
    | _ => 0
  | 0, (0, 0, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨-6, 8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨9, 8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 0, (0, 0, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨6, 8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨-9, 8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 0, (0, 0, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, 1⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-2, 14⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨-15, -3⟩
    | _ => 0
  | 0, (0, 1, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, 1⟩
    | 2 => ⟨4, 4⟩
    | 3 => ⟨14, 14⟩
    | 4 => ⟨4, 4⟩
    | 5 => ⟨-3, -3⟩
    | _ => 0
  | 0, (0, 1, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨-6, 8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨9, 8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 0, (0, 1, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨-6, 8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨9, 8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 0, (0, 1, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, 3⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-14, 2⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨3, 15⟩
    | _ => 0
  | 0, (0, 1, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨6, 8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨-9, 8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 0, (0, 1, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, 3⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-14, 2⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨3, 15⟩
    | _ => 0
  | 0, (0, 1, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, 1⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-2, 14⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨-15, -3⟩
    | _ => 0
  | 0, (0, 1, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨3, 0⟩
    | _ => 0
  | 0, (1, 0, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, 1⟩
    | 2 => ⟨4, 4⟩
    | 3 => ⟨14, 14⟩
    | 4 => ⟨4, 4⟩
    | 5 => ⟨-3, -3⟩
    | _ => 0
  | 0, (1, 0, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨6, 8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨-9, 8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 0, (1, 0, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨-6, 8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨9, 8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 0, (1, 0, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, 1⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-2, 14⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨-15, -3⟩
    | _ => 0
  | 0, (1, 0, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨-6, 8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨9, 8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 0, (1, 0, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, 3⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-14, 2⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨3, 15⟩
    | _ => 0
  | 0, (1, 0, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, 3⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-14, 2⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨3, 15⟩
    | _ => 0
  | 0, (1, 0, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨3, 0⟩
    | _ => 0
  | 0, (1, 1, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨6, 8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨-9, 8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 0, (1, 1, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, 1⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-2, 14⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨-15, -3⟩
    | _ => 0
  | 0, (1, 1, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, 3⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-14, 2⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨3, 15⟩
    | _ => 0
  | 0, (1, 1, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨3, 0⟩
    | _ => 0
  | 0, (1, 1, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, 1⟩
    | 2 => ⟨4, -4⟩
    | 3 => ⟨-2, 14⟩
    | 4 => ⟨4, -4⟩
    | 5 => ⟨-15, -3⟩
    | _ => 0
  | 0, (1, 1, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨3, 0⟩
    | _ => 0
  | 0, (1, 1, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨3, 0⟩
    | _ => 0
  | 0, (1, 1, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-5, -5⟩
    | 2 => ⟨20, 20⟩
    | 3 => ⟨-30, -30⟩
    | 4 => ⟨20, 20⟩
    | 5 => ⟨-9, -9⟩
    | _ => 0
  | 1, (0, 0, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-5, 5⟩
    | 2 => ⟨-20, 20⟩
    | 3 => ⟨-30, 30⟩
    | 4 => ⟨-20, 20⟩
    | 5 => ⟨-9, 9⟩
    | _ => 0
  | 1, (0, 0, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨-22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨-3, 0⟩
    | _ => 0
  | 1, (0, 0, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨-22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨-3, 0⟩
    | _ => 0
  | 1, (0, 0, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, -1⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-2, -14⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨-15, 3⟩
    | _ => 0
  | 1, (0, 0, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨-22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨-3, 0⟩
    | _ => 0
  | 1, (0, 0, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, -3⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-14, -2⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨3, -15⟩
    | _ => 0
  | 1, (0, 0, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, -1⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-2, -14⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨-15, 3⟩
    | _ => 0
  | 1, (0, 0, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨6, -8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨-9, -8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 1, (0, 1, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨-22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨-3, 0⟩
    | _ => 0
  | 1, (0, 1, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, -3⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-14, -2⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨3, -15⟩
    | _ => 0
  | 1, (0, 1, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, -3⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-14, -2⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨3, -15⟩
    | _ => 0
  | 1, (0, 1, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨-6, -8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨9, -8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 1, (0, 1, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, -1⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-2, -14⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨-15, 3⟩
    | _ => 0
  | 1, (0, 1, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨-6, -8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨9, -8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 1, (0, 1, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨6, -8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨-9, -8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 1, (0, 1, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, -1⟩
    | 2 => ⟨-4, 4⟩
    | 3 => ⟨14, -14⟩
    | 4 => ⟨-4, 4⟩
    | 5 => ⟨-3, 3⟩
    | _ => 0
  | 1, (1, 0, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨-3, 0⟩
    | 2 => ⟨-10, 0⟩
    | 3 => ⟨-22, 0⟩
    | 4 => ⟨-25, 0⟩
    | 5 => ⟨-3, 0⟩
    | _ => 0
  | 1, (1, 0, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, -1⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-2, -14⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨-15, 3⟩
    | _ => 0
  | 1, (1, 0, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, -3⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-14, -2⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨3, -15⟩
    | _ => 0
  | 1, (1, 0, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨6, -8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨-9, -8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 1, (1, 0, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-1, -3⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-14, -2⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨3, -15⟩
    | _ => 0
  | 1, (1, 0, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨-6, -8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨9, -8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 1, (1, 0, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨-6, -8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨9, -8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 1, (1, 0, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, -1⟩
    | 2 => ⟨-4, 4⟩
    | 3 => ⟨14, -14⟩
    | 4 => ⟨-4, 4⟩
    | 5 => ⟨-3, 3⟩
    | _ => 0
  | 1, (1, 1, 0, 0, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨-3, -1⟩
    | 2 => ⟨-4, -4⟩
    | 3 => ⟨-2, -14⟩
    | 4 => ⟨-4, -4⟩
    | 5 => ⟨-15, 3⟩
    | _ => 0
  | 1, (1, 1, 0, 0, 1), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨6, -8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨-9, -8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 1, (1, 1, 0, 1, 0), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-1, 0⟩
    | 2 => ⟨-6, -8⟩
    | 3 => ⟨6, 0⟩
    | 4 => ⟨9, -8⟩
    | 5 => ⟨-9, 0⟩
    | _ => 0
  | 1, (1, 1, 0, 1, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, -1⟩
    | 2 => ⟨-4, 4⟩
    | 3 => ⟨14, -14⟩
    | 4 => ⟨-4, 4⟩
    | 5 => ⟨-3, 3⟩
    | _ => 0
  | 1, (1, 1, 1, 0, 0), k =>
    match k.val with
    | 0 => ⟨-1, 0⟩
    | 1 => ⟨1, 0⟩
    | 2 => ⟨6, -8⟩
    | 3 => ⟨-6, 0⟩
    | 4 => ⟨-9, -8⟩
    | 5 => ⟨9, 0⟩
    | _ => 0
  | 1, (1, 1, 1, 0, 1), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, -1⟩
    | 2 => ⟨-4, 4⟩
    | 3 => ⟨14, -14⟩
    | 4 => ⟨-4, 4⟩
    | 5 => ⟨-3, 3⟩
    | _ => 0
  | 1, (1, 1, 1, 1, 0), k =>
    match k.val with
    | 0 => ⟨0, 0⟩
    | 1 => ⟨1, -1⟩
    | 2 => ⟨-4, 4⟩
    | 3 => ⟨14, -14⟩
    | 4 => ⟨-4, 4⟩
    | 5 => ⟨-3, 3⟩
    | _ => 0
  | 1, (1, 1, 1, 1, 1), k =>
    match k.val with
    | 0 => ⟨1, 0⟩
    | 1 => ⟨-5, 0⟩
    | 2 => ⟨10, 0⟩
    | 3 => ⟨-10, 0⟩
    | 4 => ⟨25, 0⟩
    | 5 => ⟨-21, 0⟩
    | _ => 0
theorem arrayTable_0_00 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 0 (0, 0, b2, b3, b4) k =
      arrayTarget 0 (0, 0, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_0_01 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 0 (0, 1, b2, b3, b4) k =
      arrayTarget 0 (0, 1, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_0_10 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 0 (1, 0, b2, b3, b4) k =
      arrayTarget 0 (1, 0, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_0_11 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 0 (1, 1, b2, b3, b4) k =
      arrayTarget 0 (1, 1, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_1_00 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 1 (0, 0, b2, b3, b4) k =
      arrayTarget 1 (0, 0, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_1_01 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 1 (0, 1, b2, b3, b4) k =
      arrayTarget 1 (0, 1, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_1_10 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 1 (1, 0, b2, b3, b4) k =
      arrayTarget 1 (1, 0, b2, b3, b4) k := by
  decide +kernel
theorem arrayTable_1_11 : ∀ b2 b3 b4 : Fin 2, ∀ k : Fin 6,
    arrayRowFor 1 (1, 1, b2, b3, b4) k =
      arrayTarget 1 (1, 1, b2, b3, b4) k := by
  decide +kernel
theorem arrayAllRows : ∀ input : Fin 2, ∀ left : FiveBitTuple, ∀ k : Fin 6,
    arrayRowFor input left k = arrayTarget input left k := by
  intro input left
  rcases left with ⟨b0, b1, b2, b3, b4⟩
  fin_cases input <;> fin_cases b0 <;> fin_cases b1
  · exact arrayTable_0_00 b2 b3 b4
  · exact arrayTable_0_01 b2 b3 b4
  · exact arrayTable_0_10 b2 b3 b4
  · exact arrayTable_0_11 b2 b3 b4
  · exact arrayTable_1_00 b2 b3 b4
  · exact arrayTable_1_01 b2 b3 b4
  · exact arrayTable_1_10 b2 b3 b4
  · exact arrayTable_1_11 b2 b3 b4
theorem arrayAmplitudeOne_complex (right : FiveBitTuple) :
    GaussianInt.toComplex (arrayAmplitudeOne right) / 4 =
      fiveQubitLogicalAmplitude 1 right := by
  rcases right with ⟨r0, r1, r2, r3, r4⟩
  fin_cases r0 <;> fin_cases r1 <;> fin_cases r2 <;>
    fin_cases r3 <;> fin_cases r4 <;>
    norm_num [arrayAmplitudeOne, fiveQubitLogicalAmplitude,
      fiveQubitLogicalOneAmplitude, GaussianInt.toComplex_def]
theorem arrayAmplitude_complex (input : Fin 2) (right : FiveBitTuple) :
    GaussianInt.toComplex (arrayAmplitude input right) / 4 =
      fiveQubitLogicalAmplitude input right := by
  fin_cases input
  · simpa only [arrayAmplitude, Fin.mk_zero, Fin.mk_one] using arrayAmplitudeZero_complex right
  · simpa only [arrayAmplitude, Fin.mk_zero, Fin.mk_one] using arrayAmplitudeOne_complex right
theorem arrayEval_row_complex_all (d : Complex) (input : Fin 2) (left : FiveBitTuple) :
    arrayEval (arrayRowFor input left) d / 128 =
      fiveQubitPreparedRowScalar d input left := by
  unfold arrayEval arrayRowFor fiveQubitPreparedRowScalar
  simp only [map_sum, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.sum_div]
  change arrayEval (arrayProductFor input left right) d / 128 = _
  rw [arrayProductFor, arrayEval_five_linear]
  rw [← arrayEntry_complex d left.1 right.1,
    ← arrayEntry_complex d left.2.1 right.2.1,
    ← arrayEntry_complex d left.2.2.1 right.2.2.1,
    ← arrayEntry_complex d left.2.2.2.1 right.2.2.2.1,
    ← arrayEntry_complex d left.2.2.2.2 right.2.2.2.2,
    ← arrayAmplitude_complex input right]
  ring
attribute [local irreducible] arrayTarget
set_option maxHeartbeats 8000000 in
theorem fiveQubitLogicalPrepared_matrixEntry_exact
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (fiveQubitLogicalCodeword output)
        ((fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)).toOperator
          (fiveQubitLogicalCodeword input)) =
      (fiveQubitRawTZeroCoefficient epsilon : Complex) *
          tDiagonalMatrixEntry 0 output input +
        (fiveQubitRawTOneCoefficient epsilon : Complex) *
          tDiagonalMatrixEntry 1 output input := by
  rw [fiveQubitLogicalPrepared_matrixEntry_sum]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (∑ left : FiveBitTuple,
    star (fiveQubitLogicalAmplitude output left) *
      fiveQubitPreparedMatrixRow epsilon input left) = _
  have hsqrtInv :
      (((Real.sqrt 3)⁻¹ : Real) : Complex) ^ 2 = 1 / 3 := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3)]
    norm_num
  have hsqrtInv' :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 2 = 1 / 3 := by
    simpa using hsqrtInv
  have hsqrtInvCube :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 3 =
        (Real.sqrt 3 : Complex)⁻¹ / 3 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 3 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 2 *
            (Real.sqrt 3 : Complex)⁻¹ := by ring
      _ = (Real.sqrt 3 : Complex)⁻¹ / 3 := by
        rw [hsqrtInv']
        ring
  have hsqrtInvFourth :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 4 = 1 / 9 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 4 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 2 *
            ((Real.sqrt 3 : Complex)⁻¹) ^ 2 := by ring
      _ = 1 / 9 := by
        rw [hsqrtInv']
        ring
  have hsqrtInvFifth :
      ((Real.sqrt 3 : Complex)⁻¹) ^ 5 =
        (Real.sqrt 3 : Complex)⁻¹ / 9 := by
    calc
      ((Real.sqrt 3 : Complex)⁻¹) ^ 5 =
          ((Real.sqrt 3 : Complex)⁻¹) ^ 4 *
            (Real.sqrt 3 : Complex)⁻¹ := by ring
      _ = (Real.sqrt 3 : Complex)⁻¹ / 9 := by
        rw [hsqrtInvFourth]
        ring
  have hIfifth : Complex.I ^ 5 = Complex.I := by
    norm_num [pow_succ, Complex.I_sq]
  simp_rw [fiveQubitPreparedMatrixRow_eq_scalar]
  simp_rw [← arrayEval_row_complex_all]
  simp only [arrayEval]
  simp_rw [arrayAllRows]
  fin_cases output <;> fin_cases input
  all_goals
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one]
    simp [arrayTarget, Fin.sum_univ_succ, GaussianInt.toComplex_def,
      fiveQubitLogicalAmplitude, fiveQubitLogicalZeroAmplitude,
      fiveQubitLogicalOneAmplitude, tDiagonalMatrixEntry,
      fiveQubitRawTZeroCoefficient, fiveQubitRawTOneCoefficient]
    ring_nf
    simp only [hsqrtInvCube, hsqrtInvFourth, hsqrtInvFifth, hIfifth, Complex.I_sq]
    ring
noncomputable def fiveQubitDecodedAcceptedRaw
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    Operator QubitSpace :=
  fiveQubitDecodingInstrument.branchOperator .accepted
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone)).toOperator
@[simp]
theorem tZero_matrixEntry (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (tZero.toOperator (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry 0 output input := by
  simpa only [tDiagonalInput_zero] using
    tDiagonalInput_matrixEntry 0 (by norm_num) (by norm_num) output input
@[simp]
theorem tOne_matrixEntry (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (tOne.toOperator (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry 1 output input := by
  have hentry :=
    tDiagonalInput_matrixEntry 1 (by norm_num) (by norm_num) output input
  rw [tDiagonalInput_toOperator] at hentry
  simpa [tRawInputBranch, tInputWeight, tInputComponent] using hentry
@[simp]
theorem tZero_apply_basis (output input : Fin 2) :
    (tZero.toOperator (qubitComputationalBasis input)) output =
      tDiagonalMatrixEntry 0 output input := by
  simpa only [qubitComputationalBasis_inner_state] using
    tZero_matrixEntry output input
@[simp]
theorem tOne_apply_basis (output input : Fin 2) :
    (tOne.toOperator (qubitComputationalBasis input)) output =
      tDiagonalMatrixEntry 1 output input := by
  simpa only [qubitComputationalBasis_inner_state] using
    tOne_matrixEntry output input
theorem fiveQubitDecodedAcceptedRaw_eq
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodedAcceptedRaw epsilon hzero hone =
      (fiveQubitRawTZeroCoefficient epsilon : Complex) • tZero.toOperator +
        (fiveQubitRawTOneCoefficient epsilon : Complex) • tOne.toOperator := by
  apply qubitOperator_ext_matrixEntry
  intro output input
  rw [fiveQubitDecodedAcceptedRaw,
    fiveQubitDecodingInstrument_accepted_matrixEntry,
    fiveQubitLogicalPrepared_matrixEntry_exact]
  simp
theorem fiveQubitAcceptedBornWeight_eq_success
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodingInstrument.bornWeight .accepted
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      fiveQubitSuccessProbability epsilon := by
  change Complex.re
      (LinearMap.trace Complex QubitSpace
        (fiveQubitDecodedAcceptedRaw epsilon hzero hone)) = _
  rw [fiveQubitDecodedAcceptedRaw_eq, map_add, map_smul, map_smul,
    tZero.trace_one, tOne.trace_one]
  simp [fiveQubitSuccessProbability]
theorem fiveQubitRawTZeroCoefficient_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTZeroCoefficient epsilon := by
  unfold fiveQubitRawTZeroCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  positivity
theorem fiveQubitRawTOneCoefficient_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitRawTOneCoefficient epsilon := by
  unfold fiveQubitRawTOneCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  positivity
theorem fiveQubitSuccessProbability_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitSuccessProbability epsilon := by
  unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient
    fiveQubitRawTOneCoefficient
  have hcomplement : 0 ≤ 1 - epsilon := sub_nonneg.mpr hone
  by_cases hhalf : epsilon ≤ 1 / 2
  · have hpositive : 0 < (1 - epsilon) ^ 5 := by
      exact pow_pos (by linarith) _
    positivity
  · have hpositive : 0 < epsilon ^ 5 := by
      exact pow_pos (by linarith) _
    positivity
theorem fiveQubitSuccessProbability_le_one_sixth
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitSuccessProbability epsilon ≤ 1 / 6 := by
  let q := epsilon * (1 - epsilon)
  have hqzero : 0 ≤ q := mul_nonneg hzero (sub_nonneg.mpr hone)
  have hqquarter : q ≤ 1 / 4 := by
    dsimp [q]
    nlinarith [sq_nonneg (epsilon - 1 / 2)]
  have hfactor : 0 ≤ q * (1 - 2 * q) :=
    mul_nonneg hqzero (by linarith)
  have hrewrite :
      fiveQubitSuccessProbability epsilon =
        (1 - 5 * q + 10 * q ^ 2) / 6 := by
    dsimp [q]
    unfold fiveQubitSuccessProbability fiveQubitRawTZeroCoefficient
      fiveQubitRawTOneCoefficient
    ring
  rw [hrewrite]
  nlinarith
theorem fiveQubitSuccessProbability_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 ≤ fiveQubitSuccessProbability epsilon :=
  (fiveQubitSuccessProbability_pos epsilon hzero hone).le
theorem fiveQubitSuccessProbability_le_one
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitSuccessProbability epsilon ≤ 1 := by
  linarith [fiveQubitSuccessProbability_le_one_sixth epsilon hzero hone]
theorem fiveQubitRejectedBornWeight_eq_rejection
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitDecodingInstrument.bornWeight .rejected
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      1 - fiveQubitSuccessProbability epsilon := by
  have hsum :=
    fiveQubitDecodingInstrument.sum_bornWeight_eq_one
      fiveQubitDecodingInstrument_complete
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone))
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
    at hsum
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at hsum
  rw [fiveQubitAcceptedBornWeight_eq_success] at hsum
  linarith
theorem fiveQubitRejectionProbability_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < 1 - fiveQubitSuccessProbability epsilon := by
  linarith [fiveQubitSuccessProbability_le_one_sixth epsilon hzero hone]
theorem fiveQubitAcceptedBornWeight_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitDecodingInstrument.bornWeight .accepted
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone)) := by
  rw [fiveQubitAcceptedBornWeight_eq_success]
  exact fiveQubitSuccessProbability_pos epsilon hzero hone
theorem fiveQubitRejectedBornWeight_pos
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    0 < fiveQubitDecodingInstrument.bornWeight .rejected
      (fiveQubitPrepareInput
        (fiveQubitNoisyResources epsilon hzero hone)) := by
  rw [fiveQubitRejectedBornWeight_eq_rejection]
  exact fiveQubitRejectionProbability_pos epsilon hzero hone
noncomputable def fiveQubitAcceptedConditionalBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  fiveQubitDecodingInstrument.conditionalDensity .accepted
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone))
    (fiveQubitAcceptedBornWeight_pos epsilon hzero hone)
noncomputable def fiveQubitRejectedConditionalBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  fiveQubitDecodingInstrument.conditionalDensity .rejected
    (fiveQubitPrepareInput
      (fiveQubitNoisyResources epsilon hzero hone))
    (fiveQubitRejectedBornWeight_pos epsilon hzero hone)
theorem fiveQubitDecodingOutput_decomposition_beforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDecodingInstrument.kraus.toQuantumChannel
      fiveQubitDecodingInstrument_complete).mapDensity
        (fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)) =
      outcomeMixture (fiveQubitSuccessProbability epsilon)
        (fiveQubitSuccessProbability_nonneg epsilon hzero hone)
        (fiveQubitSuccessProbability_le_one epsilon hzero hone)
        (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone)
        (fiveQubitRejectedConditionalBeforeSwap epsilon hzero hone) := by
  apply qubitDensityOperator_ext
  let prepared := fiveQubitPrepareInput
    (fiveQubitNoisyResources epsilon hzero hone)
  calc
    ((fiveQubitDecodingInstrument.kraus.toQuantumChannel
        fiveQubitDecodingInstrument_complete).mapDensity prepared).toOperator =
        ∑ outcome : DistillationOutcome,
          fiveQubitDecodingInstrument.branchOperator outcome
            prepared.toOperator :=
      (fiveQubitDecodingInstrument.sum_branchOperator_eq_mapDensity_toOperator
        fiveQubitDecodingInstrument_complete prepared).symm
    _ = fiveQubitDecodingInstrument.branchOperator .accepted
          prepared.toOperator +
        fiveQubitDecodingInstrument.branchOperator .rejected
          prepared.toOperator := by
      rw [show (Finset.univ : Finset DistillationOutcome) =
        {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
      rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    _ = (fiveQubitSuccessProbability epsilon : Complex) •
          (fiveQubitAcceptedConditionalBeforeSwap
            epsilon hzero hone).toOperator +
        ((1 - fiveQubitSuccessProbability epsilon : Real) : Complex) •
          (fiveQubitRejectedConditionalBeforeSwap
            epsilon hzero hone).toOperator := by
      unfold fiveQubitAcceptedConditionalBeforeSwap
        fiveQubitRejectedConditionalBeforeSwap
      rw [← fiveQubitDecodingInstrument.bornWeight_smul_conditionalDensity_toOperator
          .accepted prepared (fiveQubitAcceptedBornWeight_pos epsilon hzero hone),
        ← fiveQubitDecodingInstrument.bornWeight_smul_conditionalDensity_toOperator
          .rejected prepared (fiveQubitRejectedBornWeight_pos epsilon hzero hone),
        fiveQubitAcceptedBornWeight_eq_success,
        fiveQubitRejectedBornWeight_eq_rejection]
    _ = (outcomeMixture (fiveQubitSuccessProbability epsilon)
          (fiveQubitSuccessProbability_nonneg epsilon hzero hone)
          (fiveQubitSuccessProbability_le_one epsilon hzero hone)
          (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone)
          (fiveQubitRejectedConditionalBeforeSwap
            epsilon hzero hone)).toOperator := by
      simp [outcomeMixture, DensityOperator.convexCombinationOperator,
        branchState, outcomeWeight,
        show (Finset.univ : Finset DistillationOutcome) =
          {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide]
      simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
      norm_num
noncomputable def fiveQubitDecodingRunBeforeSwap
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DistillationRun QubitSpace FiveQubitSpace QubitSpace where
  resourceCount := 5
  noisyInput := fiveQubitNoisyResources epsilon hzero hone
  prepareInput := fiveQubitPrepareInput
  operation := fiveQubitDecodingInstrument.kraus.toQuantumChannel
    fiveQubitDecodingInstrument_complete
  successProbability := fiveQubitSuccessProbability epsilon
  success_nonneg := fiveQubitSuccessProbability_nonneg epsilon hzero hone
  success_le_one := fiveQubitSuccessProbability_le_one epsilon hzero hone
  acceptedOutput := fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone
  rejectedOutput := fiveQubitRejectedConditionalBeforeSwap epsilon hzero hone
  output_decomposition :=
    fiveQubitDecodingOutput_decomposition_beforeSwap epsilon hzero hone
noncomputable def fiveQubitOutputSwapChannel :
    QuantumChannel QubitSpace QubitSpace :=
  QuantumChannel.unitaryConj tOutputSwapTransport
@[simp]
theorem fiveQubitOutputSwapChannel_tZero :
    fiveQubitOutputSwapChannel.mapDensity tZero = tOne := by
  apply qubitDensityOperator_ext
  simpa [fiveQubitOutputSwapChannel,
    UnitaryTransport.conjDensity_toOperator] using
    congrArg DensityOperator.toOperator tOutputSwapTransport_tZero
@[simp]
theorem fiveQubitOutputSwapChannel_tOne :
    fiveQubitOutputSwapChannel.mapDensity tOne = tZero := by
  apply qubitDensityOperator_ext
  simpa [fiveQubitOutputSwapChannel,
    UnitaryTransport.conjDensity_toOperator] using
    congrArg DensityOperator.toOperator tOutputSwapTransport_tOne
noncomputable def fiveQubitDistillationRun
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DistillationRun QubitSpace FiveQubitSpace QubitSpace :=
  (fiveQubitDecodingRunBeforeSwap epsilon hzero hone).postprocess
    fiveQubitOutputSwapChannel
@[simp]
theorem fiveQubitDistillationRun_resourceCount
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).resourceCount = 5 :=
  rfl
@[simp]
theorem fiveQubitDistillationRun_successProbability
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).successProbability =
      fiveQubitSuccessProbability epsilon :=
  rfl
def fiveQubitAcceptedOutputWeight (epsilon : Real) : Fin 2 → Real
  | 0 => fiveQubitRawTOneCoefficient epsilon /
      fiveQubitSuccessProbability epsilon
  | 1 => fiveQubitRawTZeroCoefficient epsilon /
      fiveQubitSuccessProbability epsilon
theorem fiveQubitAcceptedOutputWeight_nonneg
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (word : Fin 2) :
    0 ≤ fiveQubitAcceptedOutputWeight epsilon word := by
  fin_cases word <;>
    simp only [fiveQubitAcceptedOutputWeight] <;>
    exact div_nonneg
      (by first
        | exact fiveQubitRawTOneCoefficient_nonneg epsilon hzero hone
        | exact fiveQubitRawTZeroCoefficient_nonneg epsilon hzero hone)
      (fiveQubitSuccessProbability_nonneg epsilon hzero hone)
theorem fiveQubitAcceptedOutputWeight_sum
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    ∑ word : Fin 2, fiveQubitAcceptedOutputWeight epsilon word = 1 := by
  rw [Fin.sum_univ_two]
  simp only [fiveQubitAcceptedOutputWeight]
  have hne :=
    (fiveQubitSuccessProbability_pos epsilon hzero hone).ne'
  field_simp [hne]
  unfold fiveQubitSuccessProbability
  ring
noncomputable def fiveQubitAcceptedOutput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ
    (fiveQubitAcceptedOutputWeight epsilon) tInputComponent
    (by
      intro word _hword
      exact fiveQubitAcceptedOutputWeight_nonneg
        epsilon hzero hone word)
    (by simpa using
      fiveQubitAcceptedOutputWeight_sum epsilon hzero hone)
noncomputable def fiveQubitIndependentInputErrorModel
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    IndependentInputErrorModel 5 QubitSpace where
  rate := fun _ => epsilon
  rate_nonneg := fun _ => hzero
  rate_le_one := fun _ => hone
  admissible := fun rates inputs =>
    rates = (fun _ => epsilon) ∧
      inputs = fiveQubitNoisyResources epsilon hzero hone
noncomputable def fiveQubitMagicStateProtocol
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    MagicStateDistillationProtocol QubitSpace FiveQubitSpace QubitSpace where
  run := fiveQubitDistillationRun epsilon hzero hone
  inputErrorModel := .independent
    (fiveQubitIndependentInputErrorModel epsilon hzero hone)
  inputPermitted := by
    exact ⟨rfl, rfl⟩
  behavior := .postselected
  idealOutput := tZero
  outputError := fun rho _sigma => tInputError rho
  outputError_nonneg := by
    intro rho _sigma
    unfold tInputError tInputSquaredOverlap
    linarith [projectionSquaredOverlap_le_one
      (tProjector tZeroDirection) rho
      (tProjector_isSymmetricProjection tZeroDirection)]
end BK05T
end Distillation
end QEC


