-- Prove2me | Definitions.Def_QEC_Distillation_FiveQubitT_Postselection_Part1_QECert
-- name    : QEC_Distillation_FiveQubitT_Postselection_Part1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-17T18:47:49.245764+00:00
-- url     : https://prove2.me/theorems/7cbfb265-1212-4ffc-ad76-5ab127e2d8ec
-- title:
--   FiveQubit Postselection: first literal declaration block
-- statement:
--   Definitions and structural lemmas for Postselection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Postselection.lean

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
abbrev FiveQubitSite := Fin 5
abbrev FiveQubitCheckIndex := Fin 4
abbrev FiveQubitSpace := QubitRegister FiveQubitSite
abbrev FiveQubitErrorWord := FiveQubitSite → Fin 2
inductive FiveQubitPauliLetter
  | I
  | X
  | Z
deriving DecidableEq, Repr
def fiveQubitCheckLetter
    (check : FiveQubitCheckIndex) (site : FiveQubitSite) :
    FiveQubitPauliLetter :=
  match check.1, site.1 with
  | 0, 0 => .X
  | 0, 1 => .Z
  | 0, 2 => .Z
  | 0, 3 => .X
  | 1, 1 => .X
  | 1, 2 => .Z
  | 1, 3 => .Z
  | 1, 4 => .X
  | 2, 0 => .X
  | 2, 2 => .X
  | 2, 3 => .Z
  | 2, 4 => .Z
  | 3, 0 => .Z
  | 3, 1 => .X
  | 3, 3 => .X
  | 3, 4 => .Z
  | _, _ => .I
def fiveQubitLetterX : FiveQubitPauliLetter → ZMod 2
  | .X => 1
  | _ => 0
def fiveQubitLetterZ : FiveQubitPauliLetter → ZMod 2
  | .Z => 1
  | _ => 0
def fiveQubitCheck (check : FiveQubitCheckIndex) : Binary FiveQubitSite where
  phase := 0
  vector :=
    { xPart := fun site => fiveQubitLetterX (fiveQubitCheckLetter check site)
      zPart := fun site => fiveQubitLetterZ (fiveQubitCheckLetter check site) }
theorem fiveQubitChecks_commute (left right : FiveQubitCheckIndex) :
    Commutes (fiveQubitCheck left) (fiveQubitCheck right) := by
  unfold Commutes
  fin_cases left <;> fin_cases right <;> decide +kernel
def fiveQubitCheckTarget
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    Bitstring FiveQubitSite :=
  match check.1 with
  | 0 => flipAt 0 (flipAt 3 bits)
  | 1 => flipAt 1 (flipAt 4 bits)
  | 2 => flipAt 0 (flipAt 2 bits)
  | _ => flipAt 1 (flipAt 3 bits)
def fiveQubitCheckPhase
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) : Complex :=
  match check.1 with
  | 0 => zPhase (bits 1) * zPhase (bits 2)
  | 1 => zPhase (bits 2) * zPhase (bits 3)
  | 2 => zPhase (bits 3) * zPhase (bits 4)
  | _ => zPhase (bits 0) * zPhase (bits 4)
@[simp]
theorem fiveQubitCheck_overlapCount
    (check : FiveQubitCheckIndex) :
    binaryOverlapCount (fiveQubitCheck check) = 0 := by
  fin_cases check <;> decide +kernel
@[simp]
theorem fiveQubitCheck_phase (check : FiveQubitCheckIndex) :
    (fiveQubitCheck check).phase = 0 :=
  rfl
theorem fiveQubitCheck_xSupport
    (check : FiveQubitCheckIndex) :
    xSupport (fiveQubitCheck check) =
      match check.1 with
      | 0 => {0, 3}
      | 1 => {1, 4}
      | 2 => {0, 2}
      | _ => {1, 3} := by
  fin_cases check <;> decide +kernel
theorem fiveQubitCheck_zSupport
    (check : FiveQubitCheckIndex) :
    zSupport (fiveQubitCheck check) =
      match check.1 with
      | 0 => {1, 2}
      | 1 => {2, 3}
      | 2 => {3, 4}
      | _ => {0, 4} := by
  fin_cases check <;> decide +kernel
@[simp]
theorem fiveQubitCheck_hermitianPhase
    (check : FiveQubitCheckIndex) :
    hermitianPhaseScalar (fiveQubitCheck check) = 1 := by
  simp [hermitianPhaseScalar]
@[simp]
theorem fiveQubitCheck_zSupportPhase_any
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check)) bits =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheck_zSupport, fiveQubitCheckPhase,
      zSupportPhase, supportPhaseSign]
@[simp]
theorem fiveQubitCheck_flipSupport
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    flipSupport (xSupport (fiveQubitCheck check)) bits =
      fiveQubitCheckTarget check bits := by
  fin_cases check <;> funext site <;> fin_cases site <;>
    simp [fiveQubitCheck_xSupport, fiveQubitCheckTarget,
      flipSupport, flipAt]
@[simp]
theorem fiveQubitCheck_zSupportPhase
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check))
        (flipSupport (xSupport (fiveQubitCheck check)) bits) =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheck_xSupport, fiveQubitCheck_zSupport,
      fiveQubitCheckPhase, zSupportPhase_flipSupport,
      supportPhaseSign, zSupportPhase, flipSupport]
@[simp]
theorem fiveQubitCheck_zSupportPhase_target
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    zSupportPhase (zSupport (fiveQubitCheck check))
        (fiveQubitCheckTarget check bits) =
      fiveQubitCheckPhase check bits := by
  rw [← fiveQubitCheck_flipSupport]
  exact fiveQubitCheck_zSupportPhase check bits
@[simp]
theorem fiveQubitCheckPhase_target
    (check : FiveQubitCheckIndex) (bits : Bitstring FiveQubitSite) :
    fiveQubitCheckPhase check (fiveQubitCheckTarget check bits) =
      fiveQubitCheckPhase check bits := by
  fin_cases check <;>
    simp [fiveQubitCheckPhase, fiveQubitCheckTarget, flipAt, zPhase]
set_option maxHeartbeats 1200000 in
/-- Each literal check acts by its advertised two flips and two Z signs. -/
theorem fiveQubitCheck_operator_apply
    (check : FiveQubitCheckIndex) (state : FiveQubitSpace)
    (bits : Bitstring FiveQubitSite) :
    toHermitianQubitOperator (fiveQubitCheck check) state bits =
      fiveQubitCheckPhase check bits *
        state (fiveQubitCheckTarget check bits) := by
  rw [toHermitianQubitOperator_apply, toQubitOperator_apply]
  simp only [hermitianPhaseScalar, fiveQubitCheck_overlapCount,
    pow_zero, one_mul]
  simp [binaryPhaseScalar, fiveQubitCheck_phase,
    fiveQubitCheck_flipSupport, fiveQubitCheck_zSupportPhase_target]
def fiveQubitPositiveSyndrome : JointSyndrome FiveQubitCheckIndex :=
  fun _ => StabilizerOutcome.positive
noncomputable def fiveQubitPositiveProjector : Operator FiveQubitSpace :=
  jointStabilizerProjector fiveQubitCheck fiveQubitChecks_commute
    fiveQubitPositiveSyndrome
def fiveQubitSyndromeInstrument :
    FiniteInstrument (JointSyndrome FiveQubitCheckIndex)
      (JointSyndrome FiveQubitCheckIndex) FiveQubitSpace FiveQubitSpace :=
  jointStabilizerInstrument fiveQubitCheck fiveQubitChecks_commute
theorem fiveQubitPositiveProjector_adjoint :
    LinearMap.adjoint fiveQubitPositiveProjector =
      fiveQubitPositiveProjector := by
  simpa [fiveQubitPositiveProjector] using
    jointStabilizerProjector_adjoint fiveQubitCheck
      fiveQubitChecks_commute fiveQubitPositiveSyndrome
theorem fiveQubitPositiveProjector_idempotent :
    fiveQubitPositiveProjector * fiveQubitPositiveProjector =
      fiveQubitPositiveProjector := by
  simpa [fiveQubitPositiveProjector] using
    jointStabilizerProjector_idempotent fiveQubitCheck
      fiveQubitChecks_commute fiveQubitPositiveSyndrome
noncomputable def fiveQubitAcceptedRawBranch
    (A : Operator FiveQubitSpace) : Operator FiveQubitSpace :=
  fiveQubitPositiveProjector * A * fiveQubitPositiveProjector
inductive FiveQubitSourceDecision
  | keepForDecode
  | discardBeforeDecode
deriving DecidableEq
def fiveQubitSourceDecision
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    FiveQubitSourceDecision :=
  if syndrome = fiveQubitPositiveSyndrome then
    .keepForDecode
  else
    .discardBeforeDecode
@[simp]
theorem fiveQubitSourceDecision_positive :
    fiveQubitSourceDecision fiveQubitPositiveSyndrome = .keepForDecode := by
  simp [fiveQubitSourceDecision]
def fiveQubitTechnicalOutcome
    (syndrome : JointSyndrome FiveQubitCheckIndex) :
    DistillationOutcome :=
  if syndrome = fiveQubitPositiveSyndrome then
    .accepted
  else
    .rejected
def fiveQubitPostselectionInstrument :
    FiniteInstrument (JointSyndrome FiveQubitCheckIndex) DistillationOutcome
      FiveQubitSpace FiveQubitSpace where
  kraus := jointStabilizerKrausFamily fiveQubitCheck fiveQubitChecks_commute
  observe := fiveQubitTechnicalOutcome
noncomputable def fiveQubitNoisyResources
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    Fin 5 → DensityOperator QubitSpace :=
  fun _ => tDiagonalInput epsilon hzero hone
def fiveQubitWordWeight (epsilon : Real) (word : FiveQubitErrorWord) : Real :=
  ∏ site : FiveQubitSite, tInputWeight epsilon (word site)
abbrev FiveQubitTensor : Type :=
  CompositeSystem QubitSpace
    (CompositeSystem QubitSpace
      (CompositeSystem QubitSpace
        (CompositeSystem QubitSpace QubitSpace)))
abbrev FiveBitTuple : Type :=
  Fin 2 × (Fin 2 × (Fin 2 × (Fin 2 × Fin 2)))
def fiveTupleBitstring (bits : FiveBitTuple) : Bitstring FiveQubitSite :=
  fun site =>
    match site.1 with
    | 0 => bits.1
    | 1 => bits.2.1
    | 2 => bits.2.2.1
    | 3 => bits.2.2.2.1
    | _ => bits.2.2.2.2
def splitFiveBitstring (bits : Bitstring FiveQubitSite) : FiveBitTuple :=
  (bits 0, (bits 1, (bits 2, (bits 3, bits 4))))
@[simp]
theorem splitFiveBitstring_fiveTupleBitstring (bits : FiveBitTuple) :
    splitFiveBitstring (fiveTupleBitstring bits) = bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  rfl
@[simp]
theorem fiveTupleBitstring_splitFiveBitstring
    (bits : Bitstring FiveQubitSite) :
    fiveTupleBitstring (splitFiveBitstring bits) = bits := by
  funext site
  fin_cases site <;> rfl
def fiveBitstringEquiv : FiveBitTuple ≃ Bitstring FiveQubitSite where
  toFun := fiveTupleBitstring
  invFun := splitFiveBitstring
  left_inv := splitFiveBitstring_fiveTupleBitstring
  right_inv := fiveTupleBitstring_splitFiveBitstring
noncomputable def fiveTensorRegisterTransport :
    UnitaryTransport FiveQubitTensor FiveQubitSpace := by
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let sourceBasis :=
    oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct oneBasis)))
  let targetBasis :=
    EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex
  let U := sourceBasis.equiv targetBasis fiveBitstringEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp]
theorem fiveTensorRegisterTransport_apply_basis
    (b0 b1 b2 b3 b4 : Fin 2) :
    fiveTensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex b0 ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Fin 2) Complex b1 ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Fin 2) Complex b2 ⊗ₜ[Complex]
              (EuclideanSpace.basisFun (Fin 2) Complex b3 ⊗ₜ[Complex]
                EuclideanSpace.basisFun (Fin 2) Complex b4)))) =
      EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex
        (fiveTupleBitstring (b0, b1, b2, b3, b4)) := by
  dsimp [fiveTensorRegisterTransport]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    (EuclideanSpace.basisFun (Fin 2) Complex) b3 b4]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      (EuclideanSpace.basisFun (Fin 2) Complex)) b2 (b3, b4)]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
        (EuclideanSpace.basisFun (Fin 2) Complex))) b1 (b2, b3, b4)]
  rw [← OrthonormalBasis.tensorProduct_apply
    (EuclideanSpace.basisFun (Fin 2) Complex)
    ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
      ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
        ((EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
          (EuclideanSpace.basisFun (Fin 2) Complex)))) b0 (b1, b2, b3, b4)]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
@[simp]
theorem fiveTensorRegisterTransport_symm_apply_basis
    (bits : Bitstring FiveQubitSite) :
    fiveTensorRegisterTransport.symm
        (EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex bits) =
      EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 2) ⊗ₜ[Complex]
            (EuclideanSpace.basisFun (Fin 2) Complex (bits 3) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex (bits 4)))) := by
  apply fiveTensorRegisterTransport.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [fiveTensorRegisterTransport.toLinearEquiv.apply_symm_apply]
  rw [fiveTensorRegisterTransport_apply_basis]
  exact congrArg
    (EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex)
    (fiveTupleBitstring_splitFiveBitstring bits).symm
noncomputable def fiveQubitTensorDensity
    (inputs : Fin 5 → DensityOperator QubitSpace) :
    DensityOperator FiveQubitTensor :=
  DensityOperator.tensorDensity (inputs 0)
    (DensityOperator.tensorDensity (inputs 1)
      (DensityOperator.tensorDensity (inputs 2)
        (DensityOperator.tensorDensity (inputs 3) (inputs 4))))
noncomputable def fiveQubitPrepareInput
    (inputs : Fin 5 → DensityOperator QubitSpace) :
    DensityOperator FiveQubitSpace :=
  fiveTensorRegisterTransport.conjDensity (fiveQubitTensorDensity inputs)
@[simp]
theorem fiveQubitPrepareInput_noisyResources
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    fiveQubitPrepareInput (fiveQubitNoisyResources epsilon hzero hone) =
      fiveTensorRegisterTransport.conjDensity
        (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
          (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
            (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
              (DensityOperator.tensorDensity (tDiagonalInput epsilon hzero hone)
                (tDiagonalInput epsilon hzero hone))))) :=
  rfl
noncomputable def fiveQubitComputationalBasis :
    OrthonormalBasis (Bitstring FiveQubitSite) Complex FiveQubitSpace :=
  EuclideanSpace.basisFun (Bitstring FiveQubitSite) Complex
@[simp]
theorem fiveQubitComputationalBasis_inner
    (bits : Bitstring FiveQubitSite) (state : FiveQubitSpace) :
    inner Complex (fiveQubitComputationalBasis bits) state = state bits := by
  simpa [fiveQubitComputationalBasis] using
    (EuclideanSpace.basisFun_inner
      (Bitstring FiveQubitSite) Complex state bits)
@[simp]
theorem fiveQubitComputationalBasis_apply
    (input output : Bitstring FiveQubitSite) :
    (fiveQubitComputationalBasis input).ofLp output =
      if output = input then 1 else 0 := by
  simp [fiveQubitComputationalBasis, EuclideanSpace.basisFun_apply,
    PiLp.single_apply]
def fiveQubitAllZero : Bitstring FiveQubitSite := fun _ => 0
def fiveQubitAllOne : Bitstring FiveQubitSite := fun _ => 1
@[simp]
theorem fiveQubitAllZero_ne_allOne :
    fiveQubitAllZero ≠ fiveQubitAllOne := by
  decide +kernel
noncomputable def fiveQubitLogicalZero : FiveQubitSpace :=
  (4 : Complex) •
    fiveQubitPositiveProjector
      (fiveQubitComputationalBasis fiveQubitAllZero)
noncomputable def fiveQubitLogicalOne : FiveQubitSpace :=
  (4 : Complex) •
    fiveQubitPositiveProjector
      (fiveQubitComputationalBasis fiveQubitAllOne)
theorem fiveQubitPositiveProjector_eq_four_factors :
    fiveQubitPositiveProjector =
      jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 0 *
      (jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 1 *
      (jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 2 *
       jointStabilizerFactor fiveQubitCheck fiveQubitPositiveSyndrome 3)) := by
  unfold fiveQubitPositiveProjector jointStabilizerProjector
  classical
  simp only [show (Finset.univ : Finset FiveQubitCheckIndex) =
      {0, 1, 2, 3} by decide]
  erw [Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_insert_of_notMem _ _ _ _ (by decide),
    Finset.noncommProd_singleton]
def fiveQubitLogicalZeroAmplitude : FiveBitTuple → Complex
  | (0, 0, 0, 0, 0) => 1 / 4
  | (0, 0, 0, 1, 1) => -1 / 4
  | (0, 0, 1, 0, 1) => 1 / 4
  | (0, 0, 1, 1, 0) => -1 / 4
  | (0, 1, 0, 0, 1) => 1 / 4
  | (0, 1, 0, 1, 0) => 1 / 4
  | (0, 1, 1, 0, 0) => -1 / 4
  | (0, 1, 1, 1, 1) => -1 / 4
  | (1, 0, 0, 0, 1) => -1 / 4
  | (1, 0, 0, 1, 0) => 1 / 4
  | (1, 0, 1, 0, 0) => 1 / 4
  | (1, 0, 1, 1, 1) => -1 / 4
  | (1, 1, 0, 0, 0) => -1 / 4
  | (1, 1, 0, 1, 1) => -1 / 4
  | (1, 1, 1, 0, 1) => -1 / 4
  | (1, 1, 1, 1, 0) => -1 / 4
  | _ => 0
set_option maxHeartbeats 2000000 in
@[simp]
theorem fiveQubitLogicalZero_apply_tuple (bits : FiveBitTuple) :
    fiveQubitLogicalZero (fiveTupleBitstring bits) =
      fiveQubitLogicalZeroAmplitude bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases b3 <;> fin_cases b4 <;>
    simp +decide [fiveQubitLogicalZeroAmplitude, fiveQubitLogicalZero,
      fiveQubitPositiveProjector_eq_four_factors,
      jointStabilizerFactor, stabilizerProjector,
      fiveQubitPositiveSyndrome, fiveQubitAllZero,
      fiveQubitCheckTarget, fiveQubitCheckPhase,
      fiveTupleBitstring, flipAt, zPhase,
      StabilizerOutcome.sign, Module.End.mul_apply] <;>
    norm_num
def fiveQubitLogicalOneAmplitude : FiveBitTuple → Complex
  | (0, 0, 0, 0, 1) => -1 / 4
  | (0, 0, 0, 1, 0) => -1 / 4
  | (0, 0, 1, 0, 0) => -1 / 4
  | (0, 0, 1, 1, 1) => -1 / 4
  | (0, 1, 0, 0, 0) => -1 / 4
  | (0, 1, 0, 1, 1) => 1 / 4
  | (0, 1, 1, 0, 1) => 1 / 4
  | (0, 1, 1, 1, 0) => -1 / 4
  | (1, 0, 0, 0, 0) => -1 / 4
  | (1, 0, 0, 1, 1) => -1 / 4
  | (1, 0, 1, 0, 1) => 1 / 4
  | (1, 0, 1, 1, 0) => 1 / 4
  | (1, 1, 0, 0, 1) => -1 / 4
  | (1, 1, 0, 1, 0) => 1 / 4
  | (1, 1, 1, 0, 0) => -1 / 4
  | (1, 1, 1, 1, 1) => 1 / 4
  | _ => 0
set_option maxHeartbeats 2000000 in
@[simp]
theorem fiveQubitLogicalOne_apply_tuple (bits : FiveBitTuple) :
    fiveQubitLogicalOne (fiveTupleBitstring bits) =
      fiveQubitLogicalOneAmplitude bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    fin_cases b3 <;> fin_cases b4 <;>
    simp +decide [fiveQubitLogicalOneAmplitude, fiveQubitLogicalOne,
      fiveQubitPositiveProjector_eq_four_factors,
      jointStabilizerFactor, stabilizerProjector,
      fiveQubitPositiveSyndrome, fiveQubitAllOne,
      fiveQubitCheckTarget, fiveQubitCheckPhase,
      fiveTupleBitstring, flipAt, zPhase,
      StabilizerOutcome.sign, Module.End.mul_apply] <;>
    norm_num
theorem fiveQubitPositiveProjector_isSymmetricProjection :
    fiveQubitPositiveProjector.IsSymmetricProjection := by
  refine ⟨fiveQubitPositiveProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact fiveQubitPositiveProjector_adjoint
theorem fiveQubitPositiveProjector_inner
    (left right : FiveQubitSpace) :
    inner Complex (fiveQubitPositiveProjector left)
        (fiveQubitPositiveProjector right) =
      inner Complex left (fiveQubitPositiveProjector right) := by
  calc
    inner Complex (fiveQubitPositiveProjector left)
        (fiveQubitPositiveProjector right) =
      inner Complex left
        (fiveQubitPositiveProjector
          (fiveQubitPositiveProjector right)) := by
            simpa [fiveQubitPositiveProjector_adjoint] using
              (LinearMap.adjoint_inner_right (𝕜 := Complex)
                fiveQubitPositiveProjector left
                (fiveQubitPositiveProjector right)).symm
    _ = inner Complex left (fiveQubitPositiveProjector right) := by
      have hidempotent := congrArg
        (fun operator : Operator FiveQubitSpace => operator right)
        fiveQubitPositiveProjector_idempotent
      simpa [Module.End.mul_apply] using
        congrArg (fun value : FiveQubitSpace => inner Complex left value)
          hidempotent
theorem fiveQubitPositiveProjector_anchor_zero :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllZero)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllZero)) =
      (1 / 16 : Complex) := by
  have h := fiveQubitLogicalZero_apply_tuple (0, 0, 0, 0, 0)
  change fiveQubitLogicalZero (fiveTupleBitstring (0, 0, 0, 0, 0)) = (1 / 4 : Complex) at h
  have hbits : fiveTupleBitstring (0, 0, 0, 0, 0) = fiveQubitAllZero := by
    funext i
    fin_cases i <;> rfl
  rw [hbits] at h
  change (4 : Complex) * (fiveQubitPositiveProjector
    (fiveQubitComputationalBasis fiveQubitAllZero)) fiveQubitAllZero = (1 / 4 : Complex) at h
  rw [fiveQubitComputationalBasis_inner]
  linear_combination (1 / 4 : Complex) * h
theorem fiveQubitPositiveProjector_anchor_one :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllOne)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllOne)) =
      (1 / 16 : Complex) := by
  have h := fiveQubitLogicalOne_apply_tuple (1, 1, 1, 1, 1)
  change fiveQubitLogicalOne (fiveTupleBitstring (1, 1, 1, 1, 1)) = (1 / 4 : Complex) at h
  have hbits : fiveTupleBitstring (1, 1, 1, 1, 1) = fiveQubitAllOne := by
    funext i
    fin_cases i <;> rfl
  rw [hbits] at h
  change (4 : Complex) * (fiveQubitPositiveProjector
    (fiveQubitComputationalBasis fiveQubitAllOne)) fiveQubitAllOne = (1 / 4 : Complex) at h
  rw [fiveQubitComputationalBasis_inner]
  linear_combination (1 / 4 : Complex) * h
theorem fiveQubitPositiveProjector_anchor_cross :
    inner Complex
        (fiveQubitComputationalBasis fiveQubitAllZero)
        (fiveQubitPositiveProjector
          (fiveQubitComputationalBasis fiveQubitAllOne)) =
      0 := by
  have h := fiveQubitLogicalOne_apply_tuple (0, 0, 0, 0, 0)
  change fiveQubitLogicalOne (fiveTupleBitstring (0, 0, 0, 0, 0)) = (0 : Complex) at h
  have hbits : fiveTupleBitstring (0, 0, 0, 0, 0) = fiveQubitAllZero := by
    funext i
    fin_cases i <;> rfl
  rw [hbits] at h
  change (4 : Complex) * (fiveQubitPositiveProjector
    (fiveQubitComputationalBasis fiveQubitAllOne)) fiveQubitAllZero = (0 : Complex) at h
  rw [fiveQubitComputationalBasis_inner]
  linear_combination (1 / 4 : Complex) * h
@[simp]
theorem fiveQubitLogicalZero_inner_self :
    inner Complex fiveQubitLogicalZero fiveQubitLogicalZero = 1 := by
  rw [fiveQubitLogicalZero, inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_zero]
  norm_num [map_ofNat]
@[simp]
theorem fiveQubitLogicalOne_inner_self :
    inner Complex fiveQubitLogicalOne fiveQubitLogicalOne = 1 := by
  rw [fiveQubitLogicalOne, inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_one]
  norm_num [map_ofNat]
@[simp]
theorem fiveQubitLogicalZero_inner_one :
    inner Complex fiveQubitLogicalZero fiveQubitLogicalOne = 0 := by
  rw [fiveQubitLogicalZero, fiveQubitLogicalOne,
    inner_smul_left, inner_smul_right,
    fiveQubitPositiveProjector_inner,
    fiveQubitPositiveProjector_anchor_cross]
  norm_num [map_ofNat]
@[simp]
theorem fiveQubitLogicalOne_inner_zero :
    inner Complex fiveQubitLogicalOne fiveQubitLogicalZero = 0 := by
  calc
    inner Complex fiveQubitLogicalOne fiveQubitLogicalZero =
        star (inner Complex fiveQubitLogicalZero fiveQubitLogicalOne) := by
          exact
            (inner_conj_symm
              (𝕜 := Complex)
              fiveQubitLogicalOne fiveQubitLogicalZero).symm
    _ = 0 := by simp
@[simp]
theorem fiveQubitLogicalZero_norm : ‖fiveQubitLogicalZero‖ = 1 := by
  have hsquare : ‖fiveQubitLogicalZero‖ ^ 2 = 1 := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner Complex,
      fiveQubitLogicalZero_inner_self]
    norm_num
  nlinarith [norm_nonneg fiveQubitLogicalZero]
@[simp]
theorem fiveQubitLogicalOne_norm : ‖fiveQubitLogicalOne‖ = 1 := by
  have hsquare : ‖fiveQubitLogicalOne‖ ^ 2 = 1 := by
    rw [@InnerProductSpace.norm_sq_eq_re_inner Complex,
      fiveQubitLogicalOne_inner_self]
    norm_num
  nlinarith [norm_nonneg fiveQubitLogicalOne]
@[simp]
theorem fiveQubitPositiveProjector_logicalZero :
    fiveQubitPositiveProjector fiveQubitLogicalZero =
      fiveQubitLogicalZero := by
  unfold fiveQubitLogicalZero
  rw [map_smul]
  congr 1
  change
      ((fiveQubitPositiveProjector * fiveQubitPositiveProjector)
        (fiveQubitComputationalBasis fiveQubitAllZero)) =
      fiveQubitPositiveProjector
        (fiveQubitComputationalBasis fiveQubitAllZero)
  rw [fiveQubitPositiveProjector_idempotent]
@[simp]
theorem fiveQubitPositiveProjector_logicalOne :
    fiveQubitPositiveProjector fiveQubitLogicalOne =
      fiveQubitLogicalOne := by
  unfold fiveQubitLogicalOne
  rw [map_smul]
  congr 1
  change
      ((fiveQubitPositiveProjector * fiveQubitPositiveProjector)
        (fiveQubitComputationalBasis fiveQubitAllOne)) =
      fiveQubitPositiveProjector
        (fiveQubitComputationalBasis fiveQubitAllOne)
  rw [fiveQubitPositiveProjector_idempotent]
noncomputable def fiveQubitLogicalProjector : Operator FiveQubitSpace :=
  (InnerProductSpace.rankOne Complex
    fiveQubitLogicalZero fiveQubitLogicalZero).toLinearMap +
  (InnerProductSpace.rankOne Complex
    fiveQubitLogicalOne fiveQubitLogicalOne).toLinearMap
theorem fiveQubitLogicalProjector_isSymmetricProjection :
    fiveQubitLogicalProjector.IsSymmetricProjection := by
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro state
    simp [fiveQubitLogicalProjector, Module.End.mul_apply,
      InnerProductSpace.rankOne_apply, mul_add, add_mul]
  · unfold fiveQubitLogicalProjector
    exact LinearMap.IsSymmetric.add
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) fiveQubitLogicalZero_norm).isSymmetric
      (InnerProductSpace.isSymmetricProjection_rankOne_self
        (𝕜 := Complex) fiveQubitLogicalOne_norm).isSymmetric
theorem fiveQubitLogicalProjector_range_le :
    LinearMap.range fiveQubitLogicalProjector ≤
      LinearMap.range fiveQubitPositiveProjector := by
  intro state hstate
  rcases hstate with ⟨source, rfl⟩
  refine ⟨fiveQubitLogicalProjector source, ?_⟩
  simp [fiveQubitLogicalProjector, InnerProductSpace.rankOne_apply]
theorem positiveOperator_eq_zero_of_trace_eq_zero
    {A : Operator FiveQubitSpace} (hA : LinearMap.IsPositive A)
    (htrace : LinearMap.trace Complex FiveQubitSpace A = 0) :
    A = 0 := by
  classical
  let basis := stdOrthonormalBasis Complex FiveQubitSpace
  have hmatrix :
      (LinearMap.toMatrix basis.toBasis basis.toBasis A).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff basis).2 hA
  have hmatrixTrace :
      Matrix.trace (LinearMap.toMatrix basis.toBasis basis.toBasis A) = 0 := by
    rw [← LinearMap.trace_eq_matrix_trace Complex basis.toBasis]
    exact htrace
  apply (LinearMap.toMatrix basis.toBasis basis.toBasis).injective
  simpa using (hmatrix.trace_eq_zero_iff).1 hmatrixTrace
set_option maxHeartbeats 1600000 in
theorem fiveQubitPositiveProjector_trace :
    LinearMap.trace Complex FiveQubitSpace fiveQubitPositiveProjector = 2 := by
  rw [LinearMap.trace_eq_sum_inner
    fiveQubitPositiveProjector fiveQubitComputationalBasis]
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    fiveQubitComputationalBasis_inner]
  rw [fiveQubitPositiveProjector_eq_four_factors]
  simp +decide only [jointStabilizerFactor, stabilizerProjector,
    fiveQubitPositiveSyndrome, StabilizerOutcome.sign,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, PiLp.smul_apply, PiLp.add_apply,
    ContinuousLinearMap.coe_coe, fiveQubitCheck_operator_apply,
    fiveQubitComputationalBasis_apply, fiveQubitCheckTarget,
    fiveQubitCheckPhase, fiveTupleBitstring, fiveBitstringEquiv,
    flipAt, zPhase, smul_eq_mul, one_mul, mul_one, zero_mul,
    mul_zero, add_zero, zero_add, one_smul, zero_smul]
  norm_num
theorem fiveQubitPositiveProjector_eq_logicalBasis :
    fiveQubitPositiveProjector = fiveQubitLogicalProjector := by
  have hcomplement :
      (fiveQubitPositiveProjector -
        fiveQubitLogicalProjector).IsSymmetricProjection :=
    fiveQubitLogicalProjector_isSymmetricProjection.sub_of_range_le_range
      fiveQubitPositiveProjector_isSymmetricProjection
      fiveQubitLogicalProjector_range_le
  have htrace :
      LinearMap.trace Complex FiveQubitSpace
          (fiveQubitPositiveProjector - fiveQubitLogicalProjector) = 0 := by
    rw [map_sub, fiveQubitPositiveProjector_trace]
    simp [fiveQubitLogicalProjector, map_add,
      InnerProductSpace.trace_rankOne]
    norm_num
  have hzero := positiveOperator_eq_zero_of_trace_eq_zero
    hcomplement.isPositive htrace
  exact sub_eq_zero.mp hzero
noncomputable def qubitComputationalBasis :
    OrthonormalBasis (Fin 2) Complex QubitSpace :=
  EuclideanSpace.basisFun (Fin 2) Complex
@[simp]
theorem qubitComputationalBasis_inner (left right : Fin 2) :
    inner Complex (qubitComputationalBasis left)
        (qubitComputationalBasis right) =
      if left = right then 1 else 0 :=
  qubitComputationalBasis.inner_eq_ite left right
@[simp]
theorem qubitComputationalBasis_inner_state
    (bit : Fin 2) (state : QubitSpace) :
    inner Complex (qubitComputationalBasis bit) state = state bit := by
  simpa [qubitComputationalBasis] using
    (EuclideanSpace.basisFun_inner (Fin 2) Complex state bit)
theorem qubitOperator_ext_matrixEntry
    {A B : Operator QubitSpace}
    (hentry : ∀ output input : Fin 2,
      inner Complex (qubitComputationalBasis output)
          (A (qubitComputationalBasis input)) =
        inner Complex (qubitComputationalBasis output)
          (B (qubitComputationalBasis input))) :
    A = B := by
  apply LinearMap.ext
  intro state
  rw [← qubitComputationalBasis.sum_repr' state]
  simp only [map_sum, map_smul]
  apply qubitComputationalBasis.repr.injective
  ext output
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum,
    inner_smul_right]
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [hentry output input]
theorem qubitDensityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
def tDiagonalMatrixEntry
    (epsilon : Real) (output input : Fin 2) : Complex :=
  let d : Complex := ((1 - 2 * epsilon) * (Real.sqrt 3)⁻¹ : Real)
  match output, input with
  | 0, 0 => (1 + d) / 2
  | 0, 1 => d * (1 - Complex.I) / 2
  | 1, 0 => d * (1 + Complex.I) / 2
  | 1, 1 => (1 - d) / 2
@[simp]
theorem tDiagonalInput_matrixEntry
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        ((tDiagonalInput epsilon hzero hone).toOperator
          (qubitComputationalBasis input)) =
      tDiagonalMatrixEntry epsilon output input := by
  rw [tDiagonalInput_toOperator_eq_blochProjector]
  rw [qubitComputationalBasis_inner_state]
  fin_cases output <;> fin_cases input <;>
    simp [tDiagonalMatrixEntry, qubitComputationalBasis,
      blochProjector, blochOperator_apply_zero,
      blochOperator_apply_one, tDiagonalBloch] <;>
    ring
theorem fiveQubitPrepareInput_matrixEntry
    (inputs : Fin 5 → DensityOperator QubitSpace)
    (output input : Bitstring FiveQubitSite) :
    inner Complex (fiveQubitComputationalBasis output)
        ((fiveQubitPrepareInput inputs).toOperator
          (fiveQubitComputationalBasis input)) =
      inner Complex (qubitComputationalBasis (output 0))
          ((inputs 0).toOperator (qubitComputationalBasis (input 0))) *
      inner Complex (qubitComputationalBasis (output 1))
          ((inputs 1).toOperator (qubitComputationalBasis (input 1))) *
      inner Complex (qubitComputationalBasis (output 2))
          ((inputs 2).toOperator (qubitComputationalBasis (input 2))) *
      inner Complex (qubitComputationalBasis (output 3))
          ((inputs 3).toOperator (qubitComputationalBasis (input 3))) *
      inner Complex (qubitComputationalBasis (output 4))
          ((inputs 4).toOperator (qubitComputationalBasis (input 4))) := by
  have houtput :
      fiveQubitComputationalBasis output =
        fiveTensorRegisterTransport
          (qubitComputationalBasis (output 0) ⊗ₜ[Complex]
            (qubitComputationalBasis (output 1) ⊗ₜ[Complex]
              (qubitComputationalBasis (output 2) ⊗ₜ[Complex]
                (qubitComputationalBasis (output 3) ⊗ₜ[Complex]
                  qubitComputationalBasis (output 4))))) := by
    unfold fiveQubitComputationalBasis qubitComputationalBasis
    symm
    rw [fiveTensorRegisterTransport_apply_basis]
    congr 1
    exact fiveTupleBitstring_splitFiveBitstring output
  have hinput :
      fiveTensorRegisterTransport.symm
          (fiveQubitComputationalBasis input) =
        qubitComputationalBasis (input 0) ⊗ₜ[Complex]
          (qubitComputationalBasis (input 1) ⊗ₜ[Complex]
            (qubitComputationalBasis (input 2) ⊗ₜ[Complex]
              (qubitComputationalBasis (input 3) ⊗ₜ[Complex]
                qubitComputationalBasis (input 4)))) := by
    simpa [fiveQubitComputationalBasis, qubitComputationalBasis] using
      fiveTensorRegisterTransport_symm_apply_basis input
  rw [fiveQubitPrepareInput, UnitaryTransport.conjDensity_toOperator]
  change inner Complex (fiveQubitComputationalBasis output)
      (fiveTensorRegisterTransport
        ((fiveQubitTensorDensity inputs).toOperator
          (fiveTensorRegisterTransport.symm
            (fiveQubitComputationalBasis input)))) = _
  rw [houtput, hinput, fiveTensorRegisterTransport.map_inner]
  simp [fiveQubitTensorDensity, DensityOperator.tensorDensity_toOperator,
    TensorProduct.map_tmul, TensorProduct.inner_tmul]
  ring
theorem fiveQubit_inner_operator_eq_sum
    (left right : FiveQubitSpace) (A : Operator FiveQubitSpace) :
    inner Complex left (A right) =
      ∑ output : Bitstring FiveQubitSite,
        ∑ input : Bitstring FiveQubitSite,
          star (left output) *
            inner Complex (fiveQubitComputationalBasis output)
              (A (fiveQubitComputationalBasis input)) *
            right input := by
  calc
    inner Complex left (A right) =
        inner Complex
          (∑ output : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis output) left •
              fiveQubitComputationalBasis output)
          (A (∑ input : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis input) right •
              fiveQubitComputationalBasis input)) := by
            rw [fiveQubitComputationalBasis.sum_repr',
              fiveQubitComputationalBasis.sum_repr']
    _ = _ := by
      simp only [map_sum, map_smul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right,
        fiveQubitComputationalBasis_inner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      simp only [starRingEnd_apply]
      ring
noncomputable def fiveQubitLogicalDecoderOperator :
    FiveQubitSpace →ₗ[Complex] QubitSpace :=
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 0) fiveQubitLogicalZero).toLinearMap +
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 1) fiveQubitLogicalOne).toLinearMap
@[simp]
theorem fiveQubitLogicalDecoderOperator_logicalZero :
    fiveQubitLogicalDecoderOperator fiveQubitLogicalZero =
      qubitComputationalBasis 0 := by
  simp only [fiveQubitLogicalDecoderOperator, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    fiveQubitLogicalZero_inner_self, fiveQubitLogicalOne_inner_self,
    fiveQubitLogicalZero_inner_one, fiveQubitLogicalOne_inner_zero,
    one_smul, zero_smul, add_zero, zero_add]
@[simp]
theorem fiveQubitLogicalDecoderOperator_logicalOne :
    fiveQubitLogicalDecoderOperator fiveQubitLogicalOne =
      qubitComputationalBasis 1 := by
  simp only [fiveQubitLogicalDecoderOperator, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    fiveQubitLogicalZero_inner_self, fiveQubitLogicalOne_inner_self,
    fiveQubitLogicalZero_inner_one, fiveQubitLogicalOne_inner_zero,
    one_smul, zero_smul, add_zero, zero_add]
theorem adjoint_rankOne_output_logical
    (output : QubitSpace) (logical : FiveQubitSpace) :
    LinearMap.adjoint
        (InnerProductSpace.rankOne Complex output logical).toLinearMap =
      (InnerProductSpace.rankOne Complex logical output).toLinearMap := by
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  exact congrArg ContinuousLinearMap.toLinearMap
    (InnerProductSpace.adjoint_rankOne (𝕜 := Complex) output logical)
theorem fiveQubitLogicalDecoderOperator_adjoint_comp :
    (LinearMap.adjoint fiveQubitLogicalDecoderOperator).comp
        fiveQubitLogicalDecoderOperator =
      fiveQubitPositiveProjector := by
  rw [fiveQubitPositiveProjector_eq_logicalBasis]
  unfold fiveQubitLogicalDecoderOperator
  rw [map_add, adjoint_rankOne_output_logical,
    adjoint_rankOne_output_logical]
  apply LinearMap.ext
  intro state
  have h00 : inner Complex (qubitComputationalBasis (0 : Fin 2))
      (qubitComputationalBasis 0) = 1 := by
    rw [qubitComputationalBasis_inner]; norm_num
  have h01 : inner Complex (qubitComputationalBasis (0 : Fin 2))
      (qubitComputationalBasis 1) = 0 := by
    rw [qubitComputationalBasis_inner]; norm_num
  have h10 : inner Complex (qubitComputationalBasis (1 : Fin 2))
      (qubitComputationalBasis 0) = 0 := by
    rw [qubitComputationalBasis_inner]; norm_num
  have h11 : inner Complex (qubitComputationalBasis (1 : Fin 2))
      (qubitComputationalBasis 1) = 1 := by
    rw [qubitComputationalBasis_inner]; norm_num
  simp only [fiveQubitLogicalProjector, LinearMap.comp_apply,
    LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_add_right, inner_smul_right,
    h00, h01, h10, h11, mul_one, mul_zero, add_zero, zero_add]
noncomputable def fiveQubitRejectedProjection : Operator FiveQubitSpace :=
  1 - fiveQubitPositiveProjector
theorem fiveQubitRejectedProjection_adjoint :
    LinearMap.adjoint fiveQubitRejectedProjection =
      fiveQubitRejectedProjection := by
  simp [fiveQubitRejectedProjection, fiveQubitPositiveProjector_adjoint]
theorem fiveQubitRejectedProjection_idempotent :
    fiveQubitRejectedProjection * fiveQubitRejectedProjection =
      fiveQubitRejectedProjection := by
  apply LinearMap.ext
  intro state
  have hproject := congrArg
    (fun operator : Operator FiveQubitSpace => operator state)
    fiveQubitPositiveProjector_idempotent
  simp only [Module.End.mul_apply] at hproject
  simp [fiveQubitRejectedProjection, hproject]
noncomputable def fiveQubitTechnicalRejectOperator
    (bits : Bitstring FiveQubitSite) :
    FiveQubitSpace →ₗ[Complex] QubitSpace :=
  (InnerProductSpace.rankOne Complex
    (qubitComputationalBasis 0)
    (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))).toLinearMap
theorem fiveQubitTechnicalRejectOperator_adjoint_comp
    (bits : Bitstring FiveQubitSite) :
    (LinearMap.adjoint (fiveQubitTechnicalRejectOperator bits)).comp
        (fiveQubitTechnicalRejectOperator bits) =
      (InnerProductSpace.rankOne Complex
        (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
        (fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits))).toLinearMap := by
  unfold fiveQubitTechnicalRejectOperator
  rw [adjoint_rankOne_output_logical]
  apply LinearMap.ext
  intro state
  have hunit : inner Complex (qubitComputationalBasis (0 : Fin 2))
      (qubitComputationalBasis 0) = 1 := by
    rw [qubitComputationalBasis_inner, if_pos rfl]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right, hunit, mul_one]
theorem fiveQubitRejectedProjection_sum_rankOne :
    (∑ bits : Bitstring FiveQubitSite,
      (InnerProductSpace.rankOne Complex
        (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
        (fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits))).toLinearMap) =
      fiveQubitRejectedProjection := by
  apply LinearMap.ext
  intro state
  simp only [LinearMap.sum_apply, InnerProductSpace.rankOne_apply]
  calc
    (∑ bits : Bitstring FiveQubitSite,
        inner Complex
            (fiveQubitRejectedProjection (fiveQubitComputationalBasis bits))
            state •
          fiveQubitRejectedProjection (fiveQubitComputationalBasis bits)) =
        fiveQubitRejectedProjection
          (∑ bits : Bitstring FiveQubitSite,
            inner Complex (fiveQubitComputationalBasis bits)
                (fiveQubitRejectedProjection state) •
              fiveQubitComputationalBasis bits) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro bits _hbits
      rw [map_smul]
      congr 1
      simpa [fiveQubitRejectedProjection_adjoint] using
        (LinearMap.adjoint_inner_right (𝕜 := Complex)
          fiveQubitRejectedProjection
          (fiveQubitComputationalBasis bits) state).symm
    _ = fiveQubitRejectedProjection (fiveQubitRejectedProjection state) := by
      rw [fiveQubitComputationalBasis.sum_repr']
    _ = fiveQubitRejectedProjection state := by
      have hidempotent := congrArg
        (fun operator : Operator FiveQubitSpace => operator state)
        fiveQubitRejectedProjection_idempotent
      simpa [Module.End.mul_apply] using hidempotent
abbrev FiveQubitDecodingIndex := Option (Bitstring FiveQubitSite)
noncomputable def fiveQubitDecodingKraus :
    FiniteKrausFamily FiveQubitDecodingIndex FiveQubitSpace QubitSpace where
  operator
    | none => fiveQubitLogicalDecoderOperator
    | some bits => fiveQubitTechnicalRejectOperator bits
theorem fiveQubitDecodingKraus_complete :
    fiveQubitDecodingKraus.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_option]
  change
    (LinearMap.adjoint fiveQubitLogicalDecoderOperator).comp
          fiveQubitLogicalDecoderOperator +
        ∑ bits : Bitstring FiveQubitSite,
          (LinearMap.adjoint (fiveQubitTechnicalRejectOperator bits)).comp
            (fiveQubitTechnicalRejectOperator bits) = 1
  rw [fiveQubitLogicalDecoderOperator_adjoint_comp]
  simp_rw [fiveQubitTechnicalRejectOperator_adjoint_comp]
  rw [fiveQubitRejectedProjection_sum_rankOne]
  simp [fiveQubitRejectedProjection]
def fiveQubitDecodingOutcome : FiveQubitDecodingIndex → DistillationOutcome
  | none => .accepted
  | some _ => .rejected
noncomputable def fiveQubitDecodingInstrument :
    FiniteInstrument FiveQubitDecodingIndex DistillationOutcome
      FiveQubitSpace QubitSpace where
  kraus := fiveQubitDecodingKraus
  observe := fiveQubitDecodingOutcome
theorem fiveQubitDecodingInstrument_complete :
    fiveQubitDecodingInstrument.kraus.Complete :=
  fiveQubitDecodingKraus_complete
theorem fiveQubitDecodingInstrument_accepted_branch
    (A : Operator FiveQubitSpace) :
    fiveQubitDecodingInstrument.branchOperator .accepted A =
      fiveQubitLogicalDecoderOperator.comp
        (A.comp (LinearMap.adjoint fiveQubitLogicalDecoderOperator)) := by
  rw [FiniteInstrument.branchOperator_apply, Fintype.sum_option]
  simp [fiveQubitDecodingInstrument, fiveQubitDecodingKraus,
    fiveQubitDecodingOutcome]
noncomputable def fiveQubitLogicalCodeword : Fin 2 → FiveQubitSpace
  | 0 => fiveQubitLogicalZero
  | 1 => fiveQubitLogicalOne
def fiveQubitLogicalAmplitude : Fin 2 → FiveBitTuple → Complex
  | 0 => fiveQubitLogicalZeroAmplitude
  | 1 => fiveQubitLogicalOneAmplitude
@[simp]
theorem fiveQubitLogicalCodeword_apply_tuple
    (logical : Fin 2) (bits : FiveBitTuple) :
    fiveQubitLogicalCodeword logical (fiveTupleBitstring bits) =
      fiveQubitLogicalAmplitude logical bits := by
  fin_cases logical <;>
    simp [fiveQubitLogicalCodeword, fiveQubitLogicalAmplitude]
@[simp]
theorem fiveQubitLogicalDecoderOperator_adjoint_basis
    (input : Fin 2) :
    LinearMap.adjoint fiveQubitLogicalDecoderOperator
        (qubitComputationalBasis input) =
      fiveQubitLogicalCodeword input := by
  fin_cases input <;>
    simp [fiveQubitLogicalDecoderOperator, fiveQubitLogicalCodeword,
      map_add, adjoint_rankOne_output_logical,
      InnerProductSpace.rankOne_apply]
theorem fiveQubitDecodingInstrument_accepted_matrixEntry
    (A : Operator FiveQubitSpace) (output input : Fin 2) :
    inner Complex (qubitComputationalBasis output)
        (fiveQubitDecodingInstrument.branchOperator .accepted A
          (qubitComputationalBasis input)) =
      inner Complex (fiveQubitLogicalCodeword output)
        (A (fiveQubitLogicalCodeword input)) := by
  rw [fiveQubitDecodingInstrument_accepted_branch]
  simp only [LinearMap.comp_apply,
    fiveQubitLogicalDecoderOperator_adjoint_basis]
  fin_cases output <;>
    simp [fiveQubitLogicalCodeword, fiveQubitLogicalDecoderOperator,
      InnerProductSpace.rankOne_apply]
noncomputable def tOutputSwapTransport :
    UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans
    (phaseTransport.trans
      (phaseTransport.trans
        (hadamardTransport.trans
          (phaseTransport.trans
            (phaseTransport.trans hadamardTransport)))))
theorem trans_conjDensity
    (U V : UnitaryTransport QubitSpace QubitSpace)
    (rho : DensityOperator QubitSpace) :
    (U.trans V).conjDensity rho = V.conjDensity (U.conjDensity rho) := by
  apply DensityOperator.ext_toOperator
  rfl
theorem tOutputSwapTransport_tZero :
    tOutputSwapTransport.conjDensity tZero = tOne := by
  unfold tOutputSwapTransport tZero tOne
  simp only [trans_conjDensity, hadamard_conj_tMagicState,
    phase_conj_tMagicState]
  congr 1
  decide +kernel
theorem tOutputSwapTransport_tOne :
    tOutputSwapTransport.conjDensity tOne = tZero := by
  unfold tOutputSwapTransport tZero tOne
  simp only [trans_conjDensity, hadamard_conj_tMagicState,
    phase_conj_tMagicState]
  congr 1
  decide +kernel
def fiveQubitRawTZeroCoefficient (epsilon : Real) : Real :=
  (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6
def fiveQubitRawTOneCoefficient (epsilon : Real) : Real :=
  ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6
def fiveQubitSuccessProbability (epsilon : Real) : Real :=
  fiveQubitRawTZeroCoefficient epsilon +
    fiveQubitRawTOneCoefficient epsilon
theorem fiveQubitLogicalPrepared_matrixEntry_sum
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (output input : Fin 2) :
    inner Complex (fiveQubitLogicalCodeword output)
        ((fiveQubitPrepareInput
          (fiveQubitNoisyResources epsilon hzero hone)).toOperator
          (fiveQubitLogicalCodeword input)) =
      ∑ left : FiveBitTuple, ∑ right : FiveBitTuple,
        star (fiveQubitLogicalAmplitude output left) *
          (tDiagonalMatrixEntry epsilon left.1 right.1 *
            tDiagonalMatrixEntry epsilon left.2.1 right.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.1 right.2.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.2.1 right.2.2.2.1 *
            tDiagonalMatrixEntry epsilon left.2.2.2.2 right.2.2.2.2) *
          fiveQubitLogicalAmplitude input right := by
  rw [fiveQubit_inner_operator_eq_sum]
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [← Equiv.sum_comp fiveBitstringEquiv]
  apply Finset.sum_congr rfl
  intro right _hright
  change
    star (fiveQubitLogicalCodeword output (fiveTupleBitstring left)) *
          inner Complex
            (fiveQubitComputationalBasis (fiveTupleBitstring left))
            ((fiveQubitPrepareInput
              (fiveQubitNoisyResources epsilon hzero hone)).toOperator
              (fiveQubitComputationalBasis (fiveTupleBitstring right))) *
          fiveQubitLogicalCodeword input (fiveTupleBitstring right) = _
  rw [fiveQubitLogicalCodeword_apply_tuple,
    fiveQubitLogicalCodeword_apply_tuple,
    fiveQubitPrepareInput_matrixEntry]
  simp only [fiveQubitNoisyResources, tDiagonalInput_matrixEntry]
  rfl
end BK05T
end Distillation
end QEC


