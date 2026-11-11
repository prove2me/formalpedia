-- Prove2me | Definitions.Def_QEC_Distillation_Injection_PhaseInjection
-- name    : QEC_Distillation_Injection_PhaseInjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:17:26.325571+00:00
-- url     : https://prove2.me/theorems/c2c2ba3c-f14e-4480-a965-0aac4340b16c
-- title:
--   Phase Injection
-- statement:
--   Definitions and structural lemmas for Phase Injection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseInjection.lean

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_history
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_ledger
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_postprocess_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_deterministic_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_measure
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_terminal_totalWeight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependCoin
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependDeterministic
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_map_prependSyndrome
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_ledger_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_clifford
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_discard
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_resource
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_zeroPreparation
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_operator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_weight
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_conditionalDensity_toOperator
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_ZeroPreparationAdapter_run_toOperator
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_history
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_ledger
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.postprocess_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_deterministic_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_terminal_totalWeight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependCoin
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependDeterministic
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_map_prependSyndrome
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.ledger_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_discard
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_resource
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_zeroPreparation
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_operator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
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
namespace PhaseInjection
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
noncomputable def injectionInput (psi : QubitSpace) (theta : Real) :
    TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)
def zzCheck : Binary (Fin 2) :=
  cssZCheck (fun _ : Fin 2 => (1 : ZMod 2))
theorem zzCheck_commutes : Commutes zzCheck zzCheck :=
  cssZCheck_commutes_cssZCheck _ _
def zzMeasurement : AdaptiveIdealClifford.JointMeasurement (Fin 2) (Fin 1) where
  checks := fun _ => zzCheck
  commute := by
    intro _ _
    exact zzCheck_commutes
def positiveSyndrome : JointSyndrome (Fin 1) :=
  fun _ => StabilizerOutcome.positive
def negativeSyndrome : JointSyndrome (Fin 1) :=
  fun _ => StabilizerOutcome.negative
def oneShotProjector (outcome : StabilizerOutcome) :
    Operator TwoQubit.TwoQubitSpace :=
  stabilizerProjector zzCheck outcome
theorem zzCheck_hermitianOperator :
    toHermitianQubitOperator zzCheck = TwoQubit.zzOperator := by
  ext psi bits
  simp [mul_assoc, zzCheck, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, toQubitOperator,
    binaryPhaseScalar, xSupport, zSupport, binarySupport, zSupportPhase,
    TwoQubit.zzOperator, Module.End.mul_apply, Fin.prod_univ_two]
@[simp] theorem oneShotProjector_positive :
    oneShotProjector StabilizerOutcome.positive = TwoQubit.zzEvenProjector := by
  simp [oneShotProjector, stabilizerProjector, zzCheck_hermitianOperator,
    TwoQubit.zzEvenProjector, StabilizerOutcome.sign]
@[simp] theorem oneShotProjector_negative :
    oneShotProjector StabilizerOutcome.negative = TwoQubit.zzOddProjector := by
  simp [oneShotProjector, stabilizerProjector, zzCheck_hermitianOperator,
    TwoQubit.zzOddProjector, StabilizerOutcome.sign] ; module
def oneShotRawBranch (psi : QubitSpace) (theta : Real)
    (outcome : StabilizerOutcome) : TwoQubit.TwoQubitSpace :=
  oneShotProjector outcome (injectionInput psi theta)
def oneShotWeight (psi : QubitSpace) (theta : Real)
    (outcome : StabilizerOutcome) : Real :=
  ‖oneShotRawBranch psi theta outcome‖ ^ 2
theorem oneShotRawBranch_positive (psi : QubitSpace) (theta : Real) :
    oneShotRawBranch psi theta StabilizerOutcome.positive =
      TwoQubit.zzEvenProjector (injectionInput psi theta) := by
  unfold oneShotRawBranch
  rw [oneShotProjector_positive]
theorem oneShotRawBranch_negative (psi : QubitSpace) (theta : Real) :
    oneShotRawBranch psi theta StabilizerOutcome.negative =
      TwoQubit.zzOddProjector (injectionInput psi theta) := by
  unfold oneShotRawBranch
  rw [oneShotProjector_negative]
theorem oneShotWeight_positive (psi : QubitSpace) (theta : Real) :
    oneShotWeight psi theta StabilizerOutcome.positive =
      TwoQubit.zzEvenWeight (injectionInput psi theta) := by
  unfold oneShotWeight
  rw [oneShotRawBranch_positive]
  rfl
theorem oneShotWeight_negative (psi : QubitSpace) (theta : Real) :
    oneShotWeight psi theta StabilizerOutcome.negative =
      TwoQubit.zzOddWeight (injectionInput psi theta) := by
  unfold oneShotWeight
  rw [oneShotRawBranch_negative]
  rfl
noncomputable def oneShotPostprocess :
    QuantumChannel TwoQubit.TwoQubitSpace QubitSpace :=
  QuantumChannel.comp TwoQubit.secondQubitDiscard
    (QuantumChannel.unitaryConj TwoQubit.xorTransport)
def positiveBranchOutput (psi : QubitSpace) (theta : Real)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) : QubitSpace :=
  TwoQubit.zzEvenBranchFirstQubit (injectionInput psi theta) h
def negativeBranchOutput (psi : QubitSpace) (theta : Real)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) : QubitSpace :=
  TwoQubit.zzOddBranchFirstQubit (injectionInput psi theta) h
def sourceOutcomeAngle (theta : Real) : StabilizerOutcome → Real
  | .positive => theta
  | .negative => -theta
def sourceOutcomeGlobalPhase (theta : Real) : StabilizerOutcome → Complex
  | .positive => 1
  | .negative => OneQubitMagic.phaseAmplitude theta
@[simp] theorem sourceOutcomeAngle_positive (theta : Real) :
    sourceOutcomeAngle theta StabilizerOutcome.positive = theta :=
  rfl
@[simp] theorem sourceOutcomeAngle_negative (theta : Real) :
    sourceOutcomeAngle theta StabilizerOutcome.negative = -theta :=
  rfl
@[simp] theorem sourceOutcomeGlobalPhase_positive (theta : Real) :
    sourceOutcomeGlobalPhase theta StabilizerOutcome.positive = 1 :=
  rfl
@[simp] theorem sourceOutcomeGlobalPhase_negative (theta : Real) :
    sourceOutcomeGlobalPhase theta StabilizerOutcome.negative =
      OneQubitMagic.phaseAmplitude theta :=
  rfl
theorem injectionInput_apply_coordinate
    (psi : QubitSpace) (theta : Real) (bits : Bitstring (Fin 2)) :
    injectionInput psi theta bits =
      psi (bits 0) * OneQubitMagic.phaseState theta (bits 1) := by
  have hinner := TwoQubit.tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)
  change
    inner Complex
        (TwoQubit.tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
        (TwoQubit.tensorRegisterTransport
          (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)) =
      inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
        (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta) at hinner
  rw [TwoQubit.tensorRegisterTransport_apply_basis] at hinner
  have hp : TwoQubit.pairBitstring (bits 0, bits 1) = bits := by
    simpa only [TwoQubit.splitBitstring] using
      TwoQubit.pair_splitBitstring bits
  rw [hp] at hinner
  rw [EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner
theorem xorTransport_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.xorTransport state bits = state (TwoQubit.xorBitstring bits) := by
  have hinner := TwoQubit.xorTransport.map_inner
    (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
      (TwoQubit.xorBitstring bits)) state
  change
    inner Complex
        (TwoQubit.xorTransport
          (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
            (TwoQubit.xorBitstring bits)))
        (TwoQubit.xorTransport state) =
      inner Complex
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
          (TwoQubit.xorBitstring bits)) state at hinner
  rw [TwoQubit.xorTransport_apply_basis,
    TwoQubit.xorBitstring_involutive] at hinner
  rw [EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner
theorem tensorRegisterTransport_apply_tmul_coordinate
    (x y : QubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.tensorRegisterTransport (x ⊗ₜ[Complex] y) bits =
      x (bits 0) * y (bits 1) := by
  have hinner := TwoQubit.tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (x ⊗ₜ[Complex] y)
  change
    inner Complex
        (TwoQubit.tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
        (TwoQubit.tensorRegisterTransport (x ⊗ₜ[Complex] y)) =
      inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
        (x ⊗ₜ[Complex] y) at hinner
  rw [TwoQubit.tensorRegisterTransport_apply_basis] at hinner
  have hp : TwoQubit.pairBitstring (bits 0, bits 1) = bits := by
    simpa only [TwoQubit.splitBitstring] using
      TwoQubit.pair_splitBitstring bits
  rw [hp] at hinner
  rw [EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner
theorem zzEvenProjector_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.zzEvenProjector state bits =
      if bits 0 = bits 1 then state bits else 0 := by
  unfold TwoQubit.zzEvenProjector
  change (2 : Complex)⁻¹ * (state bits + TwoQubit.zzOperator state bits) = _
  rw [TwoQubit.zzOperator_apply]
  by_cases hbits : bits 0 = bits 1
  · simp only [if_pos hbits]
    rw [hbits, zPhase_sq]
    calc
      (2 : Complex)⁻¹ * (state bits + 1 * state bits) =
          ((2 : Complex)⁻¹ * 2) * state bits := by ring
      _ = state bits := by norm_num
  · simp only [if_neg hbits]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at hbits ⊢
      generalize hsecond : bits 1 = secondBit at hbits ⊢
      fin_cases firstBit <;> fin_cases secondBit <;>
        simp_all [zPhase]
    rw [hphase]
    ring
theorem zzOddProjector_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.zzOddProjector state bits =
      if bits 0 = bits 1 then 0 else state bits := by
  unfold TwoQubit.zzOddProjector
  change (2 : Complex)⁻¹ * (state bits - TwoQubit.zzOperator state bits) = _
  rw [TwoQubit.zzOperator_apply]
  by_cases hbits : bits 0 = bits 1
  · simp only [if_pos hbits]
    rw [hbits, zPhase_sq]
    ring
  · simp only [if_neg hbits]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at hbits ⊢
      generalize hsecond : bits 1 = secondBit at hbits ⊢
      fin_cases firstBit <;> fin_cases secondBit <;>
        simp_all [zPhase]
    rw [hphase]
    calc
      (2 : Complex)⁻¹ * (state bits - (-1) * state bits) =
          ((2 : Complex)⁻¹ * 2) * state bits := by ring
      _ = state bits := by norm_num
theorem phaseAmplitude_mul_neg_angle (theta : Real) :
    OneQubitMagic.phaseAmplitude theta * OneQubitMagic.phaseAmplitude (-theta) = 1 := by
  rw [← OneQubitMagic.phaseAmplitude_add]
  simp
theorem zzEvenProjector_injectionInput
    (psi : QubitSpace) (theta : Real) :
    TwoQubit.zzEvenProjector (injectionInput psi theta) =
      (Real.sqrt 2 : Complex)⁻¹ •
        TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0)) := by
  ext bits
  rw [zzEvenProjector_apply_coordinate, injectionInput_apply_coordinate]
  simp only [PiLp.smul_apply]
  rw [xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit <;>
    simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit] <;> ring
theorem zzOddProjector_injectionInput
    (psi : QubitSpace) (theta : Real) :
    TwoQubit.zzOddProjector (injectionInput psi theta) =
      (Real.sqrt 2 : Complex)⁻¹ •
        TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1)) := by
  ext bits
  rw [zzOddProjector_apply_coordinate, injectionInput_apply_coordinate]
  simp only [PiLp.smul_apply]
  rw [xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
    ring
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
    rw [← mul_assoc (OneQubitMagic.phaseAmplitude theta)
      (OneQubitMagic.phaseAmplitude (-theta)) (psi 1),
      phaseAmplitude_mul_neg_angle, one_mul]
    ring
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
theorem phaseShiftOperator_norm (theta : Real) (psi : QubitSpace) :
    ‖OneQubitMagic.phaseShiftOperator theta psi‖ = ‖psi‖ := by
  change ‖OneQubitMagic.phaseShiftTransport theta psi‖ = ‖psi‖
  exact (OneQubitMagic.phaseShiftTransport theta).toLinearIsometryEquiv.norm_map psi
theorem zzEvenProjector_injectionInput_norm
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    ‖TwoQubit.zzEvenProjector (injectionInput psi theta)‖ = (Real.sqrt 2)⁻¹ := by
  rw [zzEvenProjector_injectionInput, norm_smul]
  have hxor :
      ‖TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0))‖ =
        ‖TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ := by
    change
      ‖TwoQubit.xorTransport.toLinearIsometryEquiv
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0))‖ = _
    exact TwoQubit.xorTransport.toLinearIsometryEquiv.norm_map _
  have htransport :
      ‖TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ =
        ‖OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex 0‖ := by
    change
      ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ = _
    exact TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map _
  rw [hxor, htransport]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg OneQubitMagic.sqrt_two_pos.le, phaseShiftOperator_norm, hpsi]
theorem zzOddProjector_injectionInput_norm
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    ‖TwoQubit.zzOddProjector (injectionInput psi theta)‖ = (Real.sqrt 2)⁻¹ := by
  rw [zzOddProjector_injectionInput, norm_smul]
  have hxor :
      ‖TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1))‖ =
        ‖TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ := by
    change
      ‖TwoQubit.xorTransport.toLinearIsometryEquiv
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1))‖ = _
    exact TwoQubit.xorTransport.toLinearIsometryEquiv.norm_map _
  have htransport :
      ‖TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ =
        ‖(OneQubitMagic.phaseAmplitude theta •
          OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex 1‖ := by
    change
      ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ = _
    exact TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map _
  rw [hxor, htransport]
  have htarget :
      ‖OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi‖ = 1 := by
    rw [norm_smul, OneQubitMagic.phaseAmplitude_norm,
      phaseShiftOperator_norm, hpsi]
    norm_num
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg OneQubitMagic.sqrt_two_pos.le, htarget]
theorem injectionInput_zzEvenWeight
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    TwoQubit.zzEvenWeight (injectionInput psi theta) = (1 / 2 : Real) := by
  unfold TwoQubit.zzEvenWeight
  rw [zzEvenProjector_injectionInput_norm psi theta hpsi]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := OneQubitMagic.sqrt_two_pos.ne'
  field_simp [hsqrt_ne]
  nlinarith [OneQubitMagic.sqrt_two_mul_self]
theorem injectionInput_zzOddWeight
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    TwoQubit.zzOddWeight (injectionInput psi theta) = (1 / 2 : Real) := by
  unfold TwoQubit.zzOddWeight
  rw [zzOddProjector_injectionInput_norm psi theta hpsi]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := OneQubitMagic.sqrt_two_pos.ne'
  field_simp [hsqrt_ne]
  nlinarith [OneQubitMagic.sqrt_two_mul_self]
theorem sqrt_half_mul_sqrt_two :
    Real.sqrt (1 / 2 : Real) * Real.sqrt 2 = 1 := by
  rw [← Real.sqrt_mul (by norm_num : 0 ≤ (1 / 2 : Real))]
  norm_num
theorem inv_sqrt_half_mul_inv_sqrt_two :
    (Real.sqrt (1 / 2 : Real) : Complex)⁻¹ *
      (Real.sqrt 2 : Complex)⁻¹ = 1 := by
  have hcast :
      (Real.sqrt (1 / 2 : Real) : Complex) *
        (Real.sqrt 2 : Complex) = 1 := by
    exact_mod_cast sqrt_half_mul_sqrt_two
  calc
    (Real.sqrt (1 / 2 : Real) : Complex)⁻¹ *
        (Real.sqrt 2 : Complex)⁻¹ =
      ((Real.sqrt 2 : Complex) *
        (Real.sqrt (1 / 2 : Real) : Complex))⁻¹ :=
      (mul_inv_rev (Real.sqrt 2 : Complex)
        (Real.sqrt (1 / 2 : Real) : Complex)).symm
    _ = ((Real.sqrt (1 / 2 : Real) : Complex) *
        (Real.sqrt 2 : Complex))⁻¹ := by
      rw [mul_comm (Real.sqrt 2 : Complex)
        (Real.sqrt (1 / 2 : Real) : Complex)]
    _ = 1 := by rw [hcast, inv_one]
theorem zzEvenBranchState_injectionInput
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) :
    TwoQubit.zzEvenBranchState (injectionInput psi theta) h =
      TwoQubit.xorTransport
        (TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)) := by
  unfold TwoQubit.zzEvenBranchState
  rw [zzEvenProjector_injectionInput,
    injectionInput_zzEvenWeight psi theta hpsi, smul_smul,
    inv_sqrt_half_mul_inv_sqrt_two, one_smul]
theorem zzOddBranchState_injectionInput
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) :
    TwoQubit.zzOddBranchState (injectionInput psi theta) h =
      TwoQubit.xorTransport
        (TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)) := by
  unfold TwoQubit.zzOddBranchState
  rw [zzOddProjector_injectionInput,
    injectionInput_zzOddWeight psi theta hpsi, smul_smul,
    inv_sqrt_half_mul_inv_sqrt_two, one_smul]
theorem positiveBranchOutput_eq_phaseShift
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) :
    positiveBranchOutput psi theta h = OneQubitMagic.phaseShiftOperator theta psi := by
  ext a
  change
    TwoQubit.zzEvenBranchState (injectionInput psi theta) h
        (TwoQubit.pairBitstring (a, TwoQubit.controlledXBit a 0)) =
      OneQubitMagic.phaseShiftOperator theta psi a
  rw [zzEvenBranchState_injectionInput psi theta hpsi h,
    xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  fin_cases a <;> simp [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
theorem negativeBranchOutput_eq_phaseShift
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) :
    negativeBranchOutput psi theta h =
      OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi := by
  ext a
  change
    TwoQubit.zzOddBranchState (injectionInput psi theta) h
        (TwoQubit.pairBitstring (a, TwoQubit.controlledXBit a 1)) =
      (OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi) a
  rw [zzOddBranchState_injectionInput psi theta hpsi h,
    xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  fin_cases a <;>
    simp [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
def OneShotCorrect (psi : QubitSpace) (theta : Real) : Prop :=
  ‖psi‖ = 1 →
    oneShotWeight psi theta StabilizerOutcome.positive = (1 / 2 : Real) ∧
      oneShotWeight psi theta StabilizerOutcome.negative = (1 / 2 : Real) ∧
      (∀ h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta),
        positiveBranchOutput psi theta h =
          sourceOutcomeGlobalPhase theta StabilizerOutcome.positive •
            OneQubitMagic.phaseShiftOperator
              (sourceOutcomeAngle theta StabilizerOutcome.positive) psi) ∧
      ∀ h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta),
        negativeBranchOutput psi theta h =
          sourceOutcomeGlobalPhase theta StabilizerOutcome.negative •
            OneQubitMagic.phaseShiftOperator
              (sourceOutcomeAngle theta StabilizerOutcome.negative) psi
theorem oneShotCorrect (psi : QubitSpace) (theta : Real) : OneShotCorrect psi theta := by
  intro hpsi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oneShotWeight_positive, injectionInput_zzEvenWeight psi theta hpsi]
  · rw [oneShotWeight_negative, injectionInput_zzOddWeight psi theta hpsi]
  · intro h
    simpa [sourceOutcomeGlobalPhase, sourceOutcomeAngle] using
      positiveBranchOutput_eq_phaseShift psi theta hpsi h
  · intro h
    simpa [sourceOutcomeGlobalPhase, sourceOutcomeAngle] using
      negativeBranchOutput_eq_phaseShift psi theta hpsi h
noncomputable def phaseStateResourceUse (theta : Real) :
    AdaptiveIdealClifford.ResourceUse
      (H := QubitSpace) (K := TwoQubit.TwoQubitSpace) (R := QubitSpace) Real where
  token := theta
  resource := OneQubitMagic.phaseStateDensity theta
  consumer := QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport
@[simp] theorem phaseStateResourceUse_ledger (theta : Real) :
    (phaseStateResourceUse theta).ledger = {theta} :=
  rfl
theorem injectionInput_norm (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) : ‖injectionInput psi theta‖ = 1 := by
  change ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)‖ = 1
  rw [TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map,
    TensorProduct.norm_tmul, hpsi, OneQubitMagic.phaseState_norm]
  norm_num
noncomputable def sourceInputDensity (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero psi (by
    intro hz
    rw [hz, norm_zero] at hpsi
    norm_num at hpsi)
noncomputable def injectionInputDensity (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) : DensityOperator TwoQubit.TwoQubitSpace :=
  DensityOperator.pureOfNonzero (injectionInput psi theta) (by
    intro hz
    have hnorm := injectionInput_norm psi theta hpsi
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm)
def observedRetryOutcome (coin : Bool) : StabilizerOutcome :=
  if coin then StabilizerOutcome.positive else StabilizerOutcome.negative
def observedRetrySyndrome (coin : Bool) : JointSyndrome (Fin 1) :=
  fun _ => observedRetryOutcome coin
def outcomeIncrement {q : Nat} : StabilizerOutcome → ZMod q
  | .positive => 1
  | .negative => -1
def observedRetryHistory (coins : List Bool) : List (JointSyndrome (Fin 1)) :=
  coins.map observedRetrySyndrome
def retryEightMissProbability (blocks : Nat) (start target : ZMod 8) : Real :=
  PhaseRetry.targetMissProbability 8 blocks start target
def retryTwelveMissProbability (blocks : Nat) (start target : ZMod 12) : Real :=
  PhaseRetry.targetMissProbability 12 blocks start target
def outcomeCoin : StabilizerOutcome → Bool
  | .positive => true
  | .negative => false
noncomputable def oneShotProjectedWeight (psi : QubitSpace) (theta : Real)
    (coin : Bool) : Real :=
  ‖jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
    (observedRetrySyndrome coin) (injectionInput psi theta)‖ ^ 2
noncomputable def oneShotInstrumentBranch (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    AdaptiveIdealClifford.RawOutcomeBranch TwoQubit.TwoQubitSpace :=
  zzMeasurement.branch (observedRetrySyndrome coin)
    ((phaseStateResourceUse theta).run (sourceInputDensity psi hpsi))
noncomputable def oneShotMeasurementWeight (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : Real :=
  (oneShotInstrumentBranch psi theta hpsi coin).weight
noncomputable def oneShotAttempt (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  if coin then
    positiveBranchOutput psi theta
      (by rw [← oneShotWeight_positive, (oneShotCorrect psi theta hpsi).1]; norm_num)
  else
    negativeBranchOutput psi theta
      (by rw [← oneShotWeight_negative, (oneShotCorrect psi theta hpsi).2.1]; norm_num)
noncomputable def oneShotAttemptAngle (theta : Real) (coin : Bool) : Real :=
  sourceOutcomeAngle theta (observedRetryOutcome coin)
noncomputable def oneShotAttemptGlobalPhase (theta : Real) (coin : Bool) : Complex :=
  sourceOutcomeGlobalPhase theta (observedRetryOutcome coin)
theorem oneShotAttempt_action (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotAttempt psi theta hpsi coin = oneShotAttemptGlobalPhase theta coin •
      OneQubitMagic.phaseShiftOperator (oneShotAttemptAngle theta coin) psi := by
  cases coin <;>
    simp [oneShotAttempt, oneShotAttemptAngle, oneShotAttemptGlobalPhase,
      observedRetryOutcome, oneShotCorrect psi theta hpsi]
theorem oneShotAttemptGlobalPhase_norm (theta : Real) (coin : Bool) :
    ‖oneShotAttemptGlobalPhase theta coin‖ = 1 := by
  cases coin <;> simp [oneShotAttemptGlobalPhase, observedRetryOutcome,
    sourceOutcomeGlobalPhase, OneQubitMagic.phaseAmplitude_norm]
theorem oneShotAttempt_norm (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    ‖oneShotAttempt psi theta hpsi coin‖ = 1 := by
  rw [oneShotAttempt_action, norm_smul, oneShotAttemptGlobalPhase_norm, one_mul]
  calc
    ‖OneQubitMagic.phaseShiftOperator (oneShotAttemptAngle theta coin) psi‖ = ‖psi‖ := by
      change ‖OneQubitMagic.phaseShiftTransport (oneShotAttemptAngle theta coin) psi‖ = ‖psi‖
      exact (OneQubitMagic.phaseShiftTransport
        (oneShotAttemptAngle theta coin)).toLinearIsometryEquiv.norm_map psi
    _ = 1 := hpsi
noncomputable def repeatedPhaseInjection (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 → QubitSpace
  | [], psi, _ => psi
  | coin :: coins, psi, hpsi =>
      repeatedPhaseInjection theta coins (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
noncomputable def repeatedPhaseInjectionTrace (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 →
      QubitSpace × AdaptiveIdealClifford.ResourceLedger Real
  | [], psi, _ => (psi, AdaptiveIdealClifford.ResourceLedger.empty Real)
  | coin :: coins, psi, hpsi =>
      let tail := repeatedPhaseInjectionTrace theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
      (tail.1, (phaseStateResourceUse theta).ledger + tail.2)
noncomputable def repeatedPhaseInjectionHistoryWeight (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 → Real
  | [], _, _ => 1
  | coin :: coins, psi, hpsi =>
      oneShotMeasurementWeight psi theta hpsi coin *
        repeatedPhaseInjectionHistoryWeight theta coins
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt_norm psi theta hpsi coin)
noncomputable def repeatedPhaseInjectionLedger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    AdaptiveIdealClifford.ResourceLedger Real :=
  (repeatedPhaseInjectionTrace theta coins psi hpsi).2
noncomputable def phaseInjectionHistoryAngle (theta : Real) : List Bool → Real
  | [] => 0
  | coin :: coins => oneShotAttemptAngle theta coin + phaseInjectionHistoryAngle theta coins
noncomputable def phaseInjectionHistoryGlobalPhase (theta : Real) : List Bool → Complex
  | [] => 1
  | coin :: coins =>
      oneShotAttemptGlobalPhase theta coin * phaseInjectionHistoryGlobalPhase theta coins
def phaseInjectionHistoryExponent : List Bool → Int
  | [] => 0
  | true :: coins => 1 + phaseInjectionHistoryExponent coins
  | false :: coins => -1 + phaseInjectionHistoryExponent coins
noncomputable def phaseCycleAngle (q : Nat) : Real := (-2 * Real.pi) / q
noncomputable def phaseCycleTargetAction (q : Nat) (target : ZMod q) :
    Operator QubitSpace :=
  OneQubitMagic.phaseShiftOperator (phaseCycleAngle q * target.val)
noncomputable def phaseEightTargetAction (target : ZMod 8) : Operator QubitSpace :=
  phaseCycleTargetAction 8 target
noncomputable def phaseTwelveTargetAction (target : ZMod 12) : Operator QubitSpace :=
  phaseCycleTargetAction 12 target
noncomputable def repeatedPhaseInjectionPhysicalTrace (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 →
      QubitSpace × (AdaptiveIdealClifford.ResourceLedger Real × Real)
  | [], psi, _ => (psi, (AdaptiveIdealClifford.ResourceLedger.empty Real, 1))
  | coin :: coins, psi, hpsi =>
      let tail := repeatedPhaseInjectionPhysicalTrace theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
      (tail.1, ((phaseStateResourceUse theta).ledger + tail.2.1,
        (oneShotInstrumentBranch psi theta hpsi coin).weight * tail.2.2))
theorem repeatedPhaseInjectionPhysicalTrace_output (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).1 =
      repeatedPhaseInjection theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      rw [repeatedPhaseInjectionPhysicalTrace, repeatedPhaseInjection]
      exact ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
def retryTraceCoins {q : Nat} :
    (blocks : Nat) → PhaseRetry.BlockTrace q blocks → List Bool
  | 0, _ => []
  | blocks + 1, trace =>
      PhaseRetry.blockCoins (trace 0) ++ retryTraceCoins blocks (fun index => trace index.succ)
def stoppingHistory {q : Nat} (start target : ZMod q) : List Bool → List Bool
  | [] => []
  | coin :: coins =>
      if start = target then [] else
        coin :: stoppingHistory (start + PhaseRetry.signedIncrement coin) target coins
noncomputable def phaseInjectionStoppingTrace {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    QubitSpace × (AdaptiveIdealClifford.ResourceLedger Real × Real) :=
  repeatedPhaseInjectionPhysicalTrace (phaseCycleAngle q)
    (stoppingHistory start target (retryTraceCoins blocks trace)) psi hpsi
noncomputable def phaseInjectionStoppingLedger {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    AdaptiveIdealClifford.ResourceLedger Real :=
  (phaseInjectionStoppingTrace start target trace psi hpsi).2.1
noncomputable def phaseInjectionStoppingMass {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  (phaseInjectionStoppingTrace start target trace psi hpsi).2.2
noncomputable def phaseInjectionStoppingMissMass {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  letI : Fintype (PhaseRetry.TargetMissTrace q blocks start target) :=
    PhaseRetry.targetMissTraceFintype q blocks start target
  ∑ trace : PhaseRetry.TargetMissTrace q blocks start target,
    phaseInjectionStoppingMass start target trace.1 psi hpsi
noncomputable def phaseInjectionStoppingHitMass {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  1 - phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi
theorem repeatedPhaseInjection_norm (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖repeatedPhaseInjection theta coins psi hpsi‖ = 1 := by
  induction coins generalizing psi with
  | nil => simpa [repeatedPhaseInjection] using hpsi
  | cons coin coins ih =>
      rw [repeatedPhaseInjection]
      exact ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
theorem phaseCycleTargetAction_norm (q : Nat) (target : ZMod q)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖phaseCycleTargetAction q target psi‖ = 1 := by
  calc
    ‖phaseCycleTargetAction q target psi‖ = ‖psi‖ := by
      change ‖OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle q * target.val) psi‖ = ‖psi‖
      exact (OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle q * target.val)).toLinearIsometryEquiv.norm_map psi
    _ = 1 := hpsi
theorem phaseInjectionStoppingTrace_output_norm {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖(phaseInjectionStoppingTrace start target trace psi hpsi).1‖ = 1 := by
  unfold phaseInjectionStoppingTrace
  rw [repeatedPhaseInjectionPhysicalTrace_output]
  exact repeatedPhaseInjection_norm _ _ _ hpsi
noncomputable def phaseInjectionStoppingOutputDensity {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero (phaseInjectionStoppingTrace start target trace psi hpsi).1
    (by
      intro hzero
      have hnorm := phaseInjectionStoppingTrace_output_norm start target trace psi hpsi
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm)
noncomputable def phaseCycleTargetOutputDensity (q : Nat) (target : ZMod q)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero (phaseCycleTargetAction q target psi)
    (by
      intro hzero
      have hnorm := phaseCycleTargetAction_norm q target psi hpsi
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm)
end PhaseInjection
end Distillation
end QEC


