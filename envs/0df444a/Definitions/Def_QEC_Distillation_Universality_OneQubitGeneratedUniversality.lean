-- Prove2me | Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
-- name    : QEC_Distillation_Universality_OneQubitGeneratedUniversality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T13:44:37.380481+00:00
-- url     : https://prove2.me/theorems/82078897-d7ad-4941-b93b-b02a9e9c470c
-- title:
--   One Qubit Generated Universality
-- statement:
--   Definitions and structural lemmas for One Qubit Generated Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitGeneratedUniversality.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
theorem generatedUniversalitySqrtTwoMulSelfComplex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self
theorem generatedUniversalitySqrtTwoNeZeroComplex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast ne_of_gt sqrt_two_pos
theorem hadamardMatrix_unitary :
    hadamardMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.conj_ofReal] <;>
    field_simp [generatedUniversalitySqrtTwoNeZeroComplex] <;>
    rw [pow_two, generatedUniversalitySqrtTwoMulSelfComplex] <;> ring
theorem phaseMatrix_unitary :
    phaseMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
theorem phaseInverseMatrix_unitary :
    phaseInverseMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseInverseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
theorem phaseShiftMatrix_unitary (theta : Real) :
    phaseShiftMatrix theta ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  change phaseAmplitude theta * star (phaseAmplitude theta) = 1
  exact phaseAmplitude_mul_conj theta
noncomputable def hadamardGate : UnitaryGate (Fin 2) :=
  ⟨hadamardMatrix, hadamardMatrix_unitary⟩
noncomputable def phaseGate : UnitaryGate (Fin 2) :=
  ⟨phaseMatrix, phaseMatrix_unitary⟩
noncomputable def phaseInverseGate : UnitaryGate (Fin 2) :=
  ⟨phaseInverseMatrix, phaseInverseMatrix_unitary⟩
noncomputable def phaseShiftGate (theta : Real) : UnitaryGate (Fin 2) :=
  ⟨phaseShiftMatrix theta, phaseShiftMatrix_unitary theta⟩
noncomputable def cliffordPhaseGenerators (theta : Real) : Set (UnitaryGate (Fin 2)) :=
  {hadamardGate, phaseGate, phaseShiftGate theta}
end QEC.Distillation.OneQubitMagic


