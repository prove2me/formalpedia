-- Prove2me | Definitions.Def_QEC_Distillation_Universality_FiniteRegisterUniversality
-- name    : QEC_Distillation_Universality_FiniteRegisterUniversality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:18:58.529202+00:00
-- url     : https://prove2.me/theorems/e9e067d8-df44-42d8-b799-fd95c7b7eff6
-- title:
--   Finite Register Universality
-- statement:
--   Definitions and structural lemmas for Finite Register Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/FiniteRegisterUniversality.lean

import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
universe u
namespace QEC
namespace Distillation
namespace FiniteRegisterUniversality
open Semantics Semantics.Qubit
open GeneratedUniversality
open scoped Kronecker
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
abbrev OtherWires (wire : Wire) : Type u := {other : Wire // other ≠ wire}
def splitAtWire (wire : Wire) (bits : Bitstring Wire) :
    Fin 2 × Bitstring (OtherWires wire) :=
  (bits wire, fun other => bits other)
def mergeAtWire (wire : Wire)
    (bits : Fin 2 × Bitstring (OtherWires wire)) : Bitstring Wire :=
  fun candidate => if h : candidate = wire then bits.1 else bits.2 ⟨candidate, h⟩
def singleQubitIndexEquiv (wire : Wire) :
    Bitstring Wire ≃ Fin 2 × Bitstring (OtherWires wire) where
  toFun := splitAtWire wire
  invFun := mergeAtWire wire
  left_inv := by
    intro bits
    funext candidate
    by_cases h : candidate = wire <;> simp [splitAtWire, mergeAtWire, h]
  right_inv := by
    rintro ⟨selected, rest⟩
    apply Prod.ext
    · simp [splitAtWire, mergeAtWire]
    · funext other
      simp [splitAtWire, mergeAtWire, other.property]
noncomputable def singleQubitLiftMatrix (wire : Wire)
    (gate : Matrix (Fin 2) (Fin 2) Complex) :
    Matrix (Bitstring Wire) (Bitstring Wire) Complex :=
  Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
    (gate ⊗ₖ (1 : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex))
noncomputable def singleQubitLiftLinear (wire : Wire) :
    Matrix (Fin 2) (Fin 2) Complex →ₗ[Complex]
      Matrix (Bitstring Wire) (Bitstring Wire) Complex where
  toFun := singleQubitLiftMatrix wire
  map_add' := by
    intro left right
    simp [singleQubitLiftMatrix, Matrix.add_kronecker, Matrix.submatrix_add]
  map_smul' := by
    intro scalar gate
    simp [singleQubitLiftMatrix, Matrix.smul_kronecker, Matrix.submatrix_smul]
noncomputable def singleQubitLift (wire : Wire)
    (gate : UnitaryGate (Fin 2)) : UnitaryGate (Bitstring Wire) := by
  refine ⟨singleQubitLiftMatrix wire gate, ?_⟩
  let indexEquiv := (singleQubitIndexEquiv wire).symm
  let localMatrix : Matrix (Fin 2) (Fin 2) Complex := gate
  let restIdentity : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex := 1
  have hlocal : localMatrix ⊗ₖ restIdentity ∈
      Matrix.unitaryGroup (Fin 2 × Bitstring (OtherWires wire)) Complex :=
    Matrix.kronecker_mem_unitary gate.property (Submonoid.one_mem _)
  apply Matrix.mem_unitaryGroup_iff.mpr
  change Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity) *
      star (Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  have hlocalEquation :
      (localMatrix ⊗ₖ restIdentity) *
        (localMatrix ⊗ₖ restIdentity).conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hlocal)
  calc
    Matrix.reindex indexEquiv indexEquiv (localMatrix ⊗ₖ restIdentity) *
        Matrix.reindex indexEquiv indexEquiv
          (localMatrix ⊗ₖ restIdentity).conjTranspose =
      Matrix.reindex indexEquiv indexEquiv
        ((localMatrix ⊗ₖ restIdentity) *
          (localMatrix ⊗ₖ restIdentity).conjTranspose) := by
      exact Matrix.reindexLinearEquiv_mul Complex Complex
        indexEquiv indexEquiv indexEquiv _ _
    _ = Matrix.reindex indexEquiv indexEquiv 1 :=
      congrArg (Matrix.reindex indexEquiv indexEquiv) hlocalEquation
    _ = 1 := Matrix.reindexLinearEquiv_one Complex Complex indexEquiv
theorem singleQubitLift_one (wire : Wire) :
    singleQubitLift wire (1 : UnitaryGate (Fin 2)) = 1 := by
  apply Subtype.ext
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      ((1 : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) = 1
  rw [Matrix.one_kronecker_one]
  exact Matrix.reindexLinearEquiv_one Complex Complex (singleQubitIndexEquiv wire).symm
theorem singleQubitLift_mul (wire : Wire) (left right : UnitaryGate (Fin 2)) :
    singleQubitLift wire (left * right) =
      singleQubitLift wire left * singleQubitLift wire right := by
  apply Subtype.ext
  change Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
      (((left : Matrix (Fin 2) (Fin 2) Complex) *
        (right : Matrix (Fin 2) (Fin 2) Complex)) ⊗ₖ
        (1 : Matrix (Bitstring (OtherWires wire))
          (Bitstring (OtherWires wire)) Complex)) =
      Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
        ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
          (1 : Matrix (Bitstring (OtherWires wire))
            (Bitstring (OtherWires wire)) Complex)) *
      Matrix.reindex (singleQubitIndexEquiv wire).symm (singleQubitIndexEquiv wire).symm
        ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ
          (1 : Matrix (Bitstring (OtherWires wire))
            (Bitstring (OtherWires wire)) Complex))
  let indexEquiv := (singleQubitIndexEquiv wire).symm
  let restIdentity : Matrix (Bitstring (OtherWires wire))
      (Bitstring (OtherWires wire)) Complex := 1
  calc
    Matrix.reindex indexEquiv indexEquiv
        (((left : Matrix (Fin 2) (Fin 2) Complex) *
          (right : Matrix (Fin 2) (Fin 2) Complex)) ⊗ₖ restIdentity) =
        Matrix.reindex indexEquiv indexEquiv
          (((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) *
            ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity)) := by
      congr 1
      rw [← Matrix.mul_kronecker_mul]
      simp [restIdentity]
    _ = Matrix.reindex indexEquiv indexEquiv
          ((left : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) *
        Matrix.reindex indexEquiv indexEquiv
          ((right : Matrix (Fin 2) (Fin 2) Complex) ⊗ₖ restIdentity) := by
      exact (Matrix.reindexLinearEquiv_mul Complex Complex
        indexEquiv indexEquiv indexEquiv _ _).symm
noncomputable def singleQubitLiftHom (wire : Wire) :
    UnitaryGate (Fin 2) →* UnitaryGate (Bitstring Wire) where
  toFun := singleQubitLift wire
  map_one' := singleQubitLift_one wire
  map_mul' := singleQubitLift_mul wire
def registerXorBitstring (control target : Wire) (_ : control ≠ target)
    (bits : Bitstring Wire) : Bitstring Wire :=
  fun wire => if wire = target then
    TwoQubit.controlledXBit (bits control) (bits target)
  else bits wire
@[simp] theorem registerXorBitstring_control (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct bits control = bits control := by
  simp [registerXorBitstring, hdistinct]
@[simp] theorem registerXorBitstring_target (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct bits target =
      TwoQubit.controlledXBit (bits control) (bits target) := by
  simp [registerXorBitstring]
@[simp] theorem registerXorBitstring_involutive (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorBitstring control target hdistinct
      (registerXorBitstring control target hdistinct bits) = bits := by
  funext wire
  by_cases htarget : wire = target
  · subst wire
    simp [registerXorBitstring, hdistinct,
      TwoQubit.controlledXBit_involutive]
  · simp [registerXorBitstring, htarget]
def registerXorBitstringEquiv (control target : Wire) (hdistinct : control ≠ target) :
    Equiv.Perm (Bitstring Wire) where
  toFun := registerXorBitstring control target hdistinct
  invFun := registerXorBitstring control target hdistinct
  left_inv := registerXorBitstring_involutive control target hdistinct
  right_inv := registerXorBitstring_involutive control target hdistinct
noncomputable def registerXorTransport (control target : Wire)
    (hdistinct : control ≠ target) :
    UnitaryTransport (QubitRegister Wire) (QubitRegister Wire) := by
  let basis := EuclideanSpace.basisFun (Bitstring Wire) Complex
  let U := basis.equiv basis (registerXorBitstringEquiv control target hdistinct)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp] theorem registerXorTransport_apply_basis (control target : Wire)
    (hdistinct : control ≠ target) (bits : Bitstring Wire) :
    registerXorTransport control target hdistinct
        (EuclideanSpace.basisFun (Bitstring Wire) Complex bits) =
      EuclideanSpace.basisFun (Bitstring Wire) Complex
        (registerXorBitstring control target hdistinct bits) := by
  dsimp [registerXorTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
noncomputable def permutationGate {n : Type u} [Fintype n] [DecidableEq n]
    (permutation : Equiv.Perm n) : UnitaryGate n := by
  refine ⟨permutation.permMatrix Complex, ?_⟩
  apply Matrix.mem_unitaryGroup_iff.mpr
  change permutation.permMatrix Complex *
      (permutation.permMatrix Complex).conjTranspose = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp
noncomputable def registerXorGate (control target : Wire)
    (hdistinct : control ≠ target) : UnitaryGate (Bitstring Wire) :=
  permutationGate (registerXorBitstringEquiv control target hdistinct)
def finiteRegisterGenerators (generators : Set (UnitaryGate (Fin 2))) :
    Set (UnitaryGate (Bitstring Wire)) :=
  {gate | ∃ wire : Wire, ∃ sourceGate : UnitaryGate (Fin 2),
    sourceGate ∈ generators ∧ gate = singleQubitLift wire sourceGate} ∪
  {gate | ∃ control target : Wire, ∃ hdistinct : control ≠ target,
    gate = registerXorGate control target hdistinct}
inductive FiniteRegisterCircuit (Wire : Type u) [Fintype Wire] [DecidableEq Wire] where
  | identity : FiniteRegisterCircuit Wire
  | oneQubit (wire : Wire) (gate : UnitaryGate (Fin 2)) : FiniteRegisterCircuit Wire
  | xor (control target : Wire) (hdistinct : control ≠ target) :
      FiniteRegisterCircuit Wire
  | compose (first second : FiniteRegisterCircuit Wire) : FiniteRegisterCircuit Wire
namespace FiniteRegisterCircuit
variable {Wire : Type u} [Fintype Wire] [DecidableEq Wire]
noncomputable def unitary : FiniteRegisterCircuit Wire → UnitaryGate (Bitstring Wire)
  | .identity => 1
  | .oneQubit wire gate => singleQubitLift wire gate
  | .xor control target hdistinct => registerXorGate control target hdistinct
  | .compose first second => second.unitary * first.unitary
end FiniteRegisterCircuit
end FiniteRegisterUniversality
end Distillation
end QEC


