-- Prove2me | Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
-- name    : QEC_Distillation_Universality_SU2AxisCircle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T14:08:05.371475+00:00
-- url     : https://prove2.me/theorems/24474c89-5750-4190-a2a8-fb7e229b64a4
-- title:
--   SU2 Axis Circle
-- statement:
--   Definitions and structural lemmas for SU2 Axis Circle, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2AxisCircle.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseInverseGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply_zero
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_matrix
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mem_cliffordPhaseGenerators
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_zero
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamardGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseInverseGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_matrix
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_mem_cliffordPhaseGenerators
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftGate_zero
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
namespace QEC
namespace Distillation
open GeneratedUniversality
structure UnitBlochAxis where
  x : Real
  y : Real
  z : Real
  norm_sq : x ^ 2 + y ^ 2 + z ^ 2 = 1
abbrev SingleQubitMatrix := Matrix (Fin 2) (Fin 2) Complex
abbrev SingleQubitGate := UnitaryGate (Fin 2)
def axisPauliMatrix (axis : UnitBlochAxis) : SingleQubitMatrix :=
  !![(axis.z : Complex), (axis.x : Complex) - Complex.I * (axis.y : Complex);
     (axis.x : Complex) + Complex.I * (axis.y : Complex), -(axis.z : Complex)]
@[simp] theorem axisPauliMatrix_zero_zero (axis : UnitBlochAxis) :
    axisPauliMatrix axis 0 0 = axis.z := by
  simp [axisPauliMatrix]
@[simp] theorem axisPauliMatrix_zero_one (axis : UnitBlochAxis) :
    axisPauliMatrix axis 0 1 =
      (axis.x : Complex) - Complex.I * (axis.y : Complex) := by
  simp [axisPauliMatrix]
@[simp] theorem axisPauliMatrix_one_zero (axis : UnitBlochAxis) :
    axisPauliMatrix axis 1 0 =
      (axis.x : Complex) + Complex.I * (axis.y : Complex) := by
  simp [axisPauliMatrix]
@[simp] theorem axisPauliMatrix_one_one (axis : UnitBlochAxis) :
    axisPauliMatrix axis 1 1 = -axis.z := by
  simp [axisPauliMatrix]
theorem axisPauliMatrix_conjTranspose (axis : UnitBlochAxis) :
    (axisPauliMatrix axis).conjTranspose = axisPauliMatrix axis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisPauliMatrix, Complex.conj_ofReal] <;> ring
theorem axisPauliMatrix_sq (axis : UnitBlochAxis) :
    axisPauliMatrix axis * axisPauliMatrix axis = 1 := by
  have hnorm : (axis.x : Complex) ^ 2 + (axis.y : Complex) ^ 2 +
      (axis.z : Complex) ^ 2 = 1 := by
    exact_mod_cast axis.norm_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisPauliMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    try rw [Complex.I_sq]
    try { convert hnorm using 1 <;> ring }
def axisLinearMatrix (axis : UnitBlochAxis) (r s : Complex) : SingleQubitMatrix :=
  r • 1 - (Complex.I * s) • axisPauliMatrix axis
theorem axisLinearMatrix_mul (axis : UnitBlochAxis) (r s u v : Complex) :
    axisLinearMatrix axis r s * axisLinearMatrix axis u v =
      axisLinearMatrix axis (r * u - s * v) (r * v + s * u) := by
  have hI : (Complex.I * v) * (Complex.I * s) = -(v * s) := by
    calc
      (Complex.I * v) * (Complex.I * s) = (Complex.I * Complex.I) * (v * s) := by ring
      _ = -(v * s) := by rw [Complex.I_mul_I]; ring
  simp only [axisLinearMatrix, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, axisPauliMatrix_sq]
  rw [smul_sub, smul_sub]
  simp only [smul_smul]
  rw [hI]
  module
def axisCircleMatrix (axis : UnitBlochAxis) (z : Complex) : SingleQubitMatrix :=
  axisLinearMatrix axis z.re z.im
@[simp] theorem axisCircleMatrix_one (axis : UnitBlochAxis) :
    axisCircleMatrix axis 1 = 1 := by
  simp [axisCircleMatrix, axisLinearMatrix]
theorem axisCircleMatrix_mul (axis : UnitBlochAxis) (z w : Complex) :
    axisCircleMatrix axis z * axisCircleMatrix axis w = axisCircleMatrix axis (z * w) := by
  rw [axisCircleMatrix, axisCircleMatrix, axisCircleMatrix, axisLinearMatrix_mul]
  simp only [Complex.mul_re, Complex.mul_im]
  norm_cast
theorem axisCircleMatrix_conjTranspose (axis : UnitBlochAxis) (z : Complex) :
    (axisCircleMatrix axis z).conjTranspose = axisCircleMatrix axis (star z) := by
  simp [axisCircleMatrix, axisLinearMatrix, axisPauliMatrix_conjTranspose,
    Complex.conj_re, Complex.conj_im]
theorem axisCircleMatrix_unitary (axis : UnitBlochAxis) (z : Circle) :
    axisCircleMatrix axis z ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, axisCircleMatrix_conjTranspose, axisCircleMatrix_mul]
  have hunit : (z : Complex) * star (z : Complex) = 1 := by
    apply Complex.ext
    · simpa [Complex.normSq_apply, pow_two] using z.normSq_coe
    · simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hunit, axisCircleMatrix_one]
def axisCircle (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) : SingleQubitGate :=
  ⟨axisCircleMatrix axis (AddCircle.toCircle t), axisCircleMatrix_unitary axis _⟩
@[simp] theorem axisCircle_matrix (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircle axis t : SingleQubitMatrix) = axisCircleMatrix axis (AddCircle.toCircle t) :=
  rfl
@[simp] theorem axisCircle_zero (axis : UnitBlochAxis) : axisCircle axis 0 = 1 := by
  apply Subtype.ext
  change axisCircleMatrix axis (AddCircle.toCircle (0 : AddCircle (2 * Real.pi))) = 1
  simp [axisCircleMatrix_one]
noncomputable def determinantRoot (U : SingleQubitGate) : Complex :=
  Classical.choose <| IsAlgClosed.exists_pow_nat_eq
    (U : SingleQubitMatrix).det (show 0 < 2 by norm_num)
theorem determinantRoot_sq (U : SingleQubitGate) :
    determinantRoot U ^ 2 = (U : SingleQubitMatrix).det := by
  exact Classical.choose_spec <| IsAlgClosed.exists_pow_nat_eq
    (U : SingleQubitMatrix).det (show 0 < 2 by norm_num)
theorem determinantRoot_norm (U : SingleQubitGate) : ‖determinantRoot U‖ = 1 := by
  have hdet_unitary : (U : SingleQubitMatrix).det ∈ unitary Complex :=
    Matrix.det_of_mem_unitary U.property
  have hdet_norm : ‖(U : SingleQubitMatrix).det‖ = 1 := by
    have hsq : ‖(U : SingleQubitMatrix).det‖ ^ 2 = 1 := by
      apply Complex.ofReal_injective
      calc
        (↑(‖(U : SingleQubitMatrix).det‖ ^ 2) : Complex) =
            (↑(Complex.normSq (U : SingleQubitMatrix).det) : Complex) := by
          rw [Complex.normSq_eq_norm_sq]
        _ = star (U : SingleQubitMatrix).det * (U : SingleQubitMatrix).det :=
          Complex.normSq_eq_conj_mul_self
        _ = 1 := hdet_unitary.1
    nlinarith [norm_nonneg ((U : SingleQubitMatrix).det)]
  have hroot_sq : ‖determinantRoot U‖ ^ 2 = 1 := by
    calc
      ‖determinantRoot U‖ ^ 2 = ‖determinantRoot U ^ 2‖ := (norm_pow _ 2).symm
      _ = ‖(U : SingleQubitMatrix).det‖ := by rw [determinantRoot_sq]
      _ = 1 := hdet_norm
  nlinarith [norm_nonneg (determinantRoot U)]
theorem determinantRoot_inv_unitary (U : SingleQubitGate) :
    (determinantRoot U)⁻¹ ∈ unitary Complex := by
  have hnormSq : Complex.normSq (determinantRoot U) = 1 := by
    rw [Complex.normSq_eq_norm_sq, determinantRoot_norm]
    norm_num
  have hstarInv : star ((determinantRoot U)⁻¹) = determinantRoot U := by
    rw [Complex.inv_def]
    simp [hnormSq]
  have hroot_ne : determinantRoot U ≠ 0 := by
    intro hzero
    simpa [hzero] using determinantRoot_norm U
  rw [Unitary.mem_iff, hstarInv]
  exact ⟨mul_inv_cancel₀ hroot_ne, inv_mul_cancel₀ hroot_ne⟩
noncomputable def phaseNormalize (U : SingleQubitGate) : SingleQubitGate :=
  ⟨(determinantRoot U)⁻¹ • (U : SingleQubitMatrix),
    Unitary.smul_mem_of_mem (determinantRoot_inv_unitary U) U.property⟩
end Distillation
end QEC


