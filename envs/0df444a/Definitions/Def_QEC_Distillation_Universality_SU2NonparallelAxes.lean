-- Prove2me | Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
-- name    : QEC_Distillation_Universality_SU2NonparallelAxes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:01:44.463198+00:00
-- url     : https://prove2.me/theorems/28b5c4d1-d400-4874-9f8b-b1d1319dc635
-- title:
--   SU2 Nonparallel Axes
-- statement:
--   Definitions and structural lemmas for SU2 Nonparallel Axes, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2NonparallelAxes.lean

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
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
import Theorems.Thm_QEC_Distillation_axisCircle_continuous
import Theorems.Thm_QEC_Distillation_axisCircle_det
import Theorems.Thm_QEC_Distillation_phaseNormalize_matrix
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
attribute [local simp] QEC.Distillation.phaseNormalize_matrix
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
open Matrix
def blochVector (axis : UnitBlochAxis) : Fin 3 → Real :=
  ![axis.x, axis.y, axis.z]
def blochDot (axis axis' : UnitBlochAxis) : Real :=
  axis.x * axis'.x + axis.y * axis'.y + axis.z * axis'.z
def blochCrossSq (axis axis' : UnitBlochAxis) : Real :=
  (axis.y * axis'.z - axis.z * axis'.y) ^ 2 +
    (axis.z * axis'.x - axis.x * axis'.z) ^ 2 +
    (axis.x * axis'.y - axis.y * axis'.x) ^ 2
def UnitBlochAxis.Nonparallel (axis axis' : UnitBlochAxis) : Prop :=
  0 < blochCrossSq axis axis'
def blochPauliMatrix (v : Fin 3 → Real) : SingleQubitMatrix :=
  !![(v 2 : Complex), (v 0 : Complex) - Complex.I * (v 1 : Complex);
     (v 0 : Complex) + Complex.I * (v 1 : Complex), -(v 2 : Complex)]
@[simp] theorem blochPauliMatrix_blochVector (axis : UnitBlochAxis) :
    blochPauliMatrix (blochVector axis) = axisPauliMatrix axis := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochPauliMatrix, blochVector, axisPauliMatrix]
@[simp] theorem blochVector_dot_self (axis : UnitBlochAxis) :
    blochVector axis ⬝ᵥ blochVector axis = 1 := by
  simp [blochVector]
  nlinarith [axis.norm_sq]
@[simp] theorem blochVector_dot (axis axis' : UnitBlochAxis) :
    blochVector axis ⬝ᵥ blochVector axis' = blochDot axis axis' := by
  simp [blochVector, blochDot]
  ring
theorem blochCrossSq_eq_one_sub_blochDot_sq (axis axis' : UnitBlochAxis) :
    blochCrossSq axis axis' = 1 - blochDot axis axis' ^ 2 := by
  have hidentity : blochCrossSq axis axis' + blochDot axis axis' ^ 2 =
      (axis.x ^ 2 + axis.y ^ 2 + axis.z ^ 2) *
        (axis'.x ^ 2 + axis'.y ^ 2 + axis'.z ^ 2) := by
    dsimp [blochCrossSq, blochDot]
    ring
  rw [axis.norm_sq, axis'.norm_sq] at hidentity
  linarith
def determinantOneSubgroup : Subgroup SingleQubitGate where
  carrier := {U | (U : SingleQubitMatrix).det = 1}
  one_mem' := by simp
  mul_mem' := by
    intro U V hU hV
    change ((U * V : SingleQubitGate) : SingleQubitMatrix).det = 1
    rw [Matrix.UnitaryGroup.mul_val, Matrix.det_mul, hU, hV, mul_one]
  inv_mem' := by
    intro U hU
    change ((U⁻¹ : SingleQubitGate) : SingleQubitMatrix).det = 1
    rw [Matrix.UnitaryGroup.inv_val]
    change ((U : SingleQubitMatrix)ᴴ).det = 1
    rw [Matrix.det_conjTranspose, hU]
    simp
abbrev SingleQubitSpecialUnitary := determinantOneSubgroup
def axisCircleSU (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    SingleQubitSpecialUnitary :=
  ⟨axisCircle axis t, axisCircle_det axis t⟩
@[simp] theorem axisCircleSU_coe (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircleSU axis t : SingleQubitGate) = axisCircle axis t := rfl
@[simp] theorem axisCircleSU_matrix (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircleSU axis t : SingleQubitMatrix) = axisCircleMatrix axis (AddCircle.toCircle t) :=
  axisCircle_matrix axis t
example : IsTopologicalGroup SingleQubitGate := by infer_instance
example : IsTopologicalGroup SingleQubitSpecialUnitary := by infer_instance
def su2Matrix (r : Real) (v : Fin 3 → Real) : SingleQubitMatrix :=
  (r : Complex) • 1 - Complex.I • blochPauliMatrix v
def su2VectorProduct (r s : Real) (v w : Fin 3 → Real) : Fin 3 → Real :=
  r • w + s • v + v ⨯₃ w
theorem su2Matrix_mul (r s : Real) (v w : Fin 3 → Real) :
    su2Matrix r v * su2Matrix s w =
      su2Matrix (r * s - v ⬝ᵥ w) (su2VectorProduct r s v w) := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1 : Complex) * Complex.I := by rw [Complex.I_sq]
      _ = -Complex.I := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, su2VectorProduct, blochPauliMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vec3_dotProduct, cross_apply] <;>
    ring_nf
  all_goals
    simp only [hI3, Complex.I_sq, Complex.I_pow_four]
    ring
theorem su2Matrix_axisLinear (axis : UnitBlochAxis) (r s : Real) :
    su2Matrix r (s • blochVector axis) = axisLinearMatrix axis r s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, blochVector, blochPauliMatrix, axisLinearMatrix, axisPauliMatrix] <;>
    ring
theorem su2Matrix_conjTranspose (r : Real) (v : Fin 3 → Real) :
    (su2Matrix r v).conjTranspose = su2Matrix r (-v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, blochPauliMatrix, Complex.conj_ofReal] <;>
    ring
@[simp] theorem blochPauliMatrix_zero : blochPauliMatrix (0 : Fin 3 → Real) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochPauliMatrix]
theorem su2Matrix_unitary (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    su2Matrix r v ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, su2Matrix_conjTranspose]
  rw [su2Matrix_mul]
  have hvec : su2VectorProduct r r v (-v) = 0 := by
    ext i
    simp [su2VectorProduct]
  rw [hvec]
  simp only [su2Matrix, blochPauliMatrix_zero, smul_zero, sub_zero]
  have hnormC : ((r ^ 2 + v ⬝ᵥ v : Real) : Complex) = 1 := by
    exact_mod_cast hnorm
  simpa [pow_two] using congrArg (fun z : Complex => z • (1 : SingleQubitMatrix)) hnormC
theorem su2Matrix_det_formula (r : Real) (v : Fin 3 → Real) :
    (su2Matrix r v).det = ((r ^ 2 + v ⬝ᵥ v : Real) : Complex) := by
  rw [Matrix.det_fin_two]
  simp [su2Matrix, blochPauliMatrix]
  rw [Matrix.vec3_dotProduct]
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_four]
  push_cast
  ring
theorem su2Matrix_det (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    (su2Matrix r v).det = 1 := by
  rw [su2Matrix_det_formula, hnorm]
  norm_num
def su2Gate (r : Real) (v : Fin 3 → Real) (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    SingleQubitSpecialUnitary :=
  ⟨⟨su2Matrix r v, su2Matrix_unitary r v hnorm⟩, su2Matrix_det r v hnorm⟩
@[simp] theorem su2Gate_matrix (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    (su2Gate r v hnorm : SingleQubitMatrix) = su2Matrix r v := rfl
theorem addCircle_toCircle_two_pi (x : Real) :
    (AddCircle.toCircle (x : AddCircle (2 * Real.pi)) : Complex) =
      (Real.cos x : Complex) + (Real.sin x : Complex) * Complex.I := by
  change (Circle.exp (2 * Real.pi / (2 * Real.pi) * x) : Complex) = _
  have hscale : 2 * Real.pi / (2 * Real.pi) * x = x := by
    field_simp [Real.pi_ne_zero]
  rw [hscale, Circle.coe_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
def axisCircleRealSU (axis : UnitBlochAxis) (x : Real) : SingleQubitSpecialUnitary :=
  axisCircleSU axis (x : AddCircle (2 * Real.pi))
@[simp] theorem axisCircleRealSU_matrix (axis : UnitBlochAxis) (x : Real) :
    (axisCircleRealSU axis x : SingleQubitMatrix) =
      su2Matrix (Real.cos x) (Real.sin x • blochVector axis) := by
  rw [axisCircleRealSU, axisCircleSU_matrix, axisCircleMatrix]
  have hz := addCircle_toCircle_two_pi x
  rw [hz]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    sub_zero, add_zero]
  simpa [zero_add] using (su2Matrix_axisLinear axis (Real.cos x) (Real.sin x)).symm
def alternatingWordFirstScalar (axis axis' : UnitBlochAxis) (x y : Real) : Real :=
  Real.cos x * Real.cos y - Real.sin x * Real.sin y * blochDot axis axis'
def alternatingWordFirstVector (axis axis' : UnitBlochAxis) (x y : Real) : Fin 3 → Real :=
  Real.cos x • (Real.sin y • blochVector axis') +
    Real.cos y • (Real.sin x • blochVector axis) +
    (Real.sin x • blochVector axis) ⨯₃ (Real.sin y • blochVector axis')
def alternatingWordScalar (axis axis' : UnitBlochAxis) (x y z : Real) : Real :=
  alternatingWordFirstScalar axis axis' x y * Real.cos z -
    alternatingWordFirstVector axis axis' x y ⬝ᵥ (Real.sin z • blochVector axis)
def alternatingWordVector (axis axis' : UnitBlochAxis) (x y z : Real) : Fin 3 → Real :=
  alternatingWordFirstScalar axis axis' x y • (Real.sin z • blochVector axis) +
    Real.cos z • alternatingWordFirstVector axis axis' x y +
    alternatingWordFirstVector axis axis' x y ⨯₃ (Real.sin z • blochVector axis)
def alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    SingleQubitSpecialUnitary :=
  axisCircleRealSU axis x * axisCircleRealSU axis' y * axisCircleRealSU axis z
theorem special_conjTranspose_eq_adjugate (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix).conjTranspose = Matrix.adjugate (U : SingleQubitMatrix) := by
  let A : SingleQubitMatrix := U
  have hunit : A * A.conjTranspose = 1 := by
    have h := U.1.property
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hadj : Matrix.adjugate A * A = 1 := by
    rw [Matrix.adjugate_mul, U.2]
    simp
  change A.conjTranspose = Matrix.adjugate A
  calc
    A.conjTranspose = 1 * A.conjTranspose := by simp
    _ = (Matrix.adjugate A * A) * A.conjTranspose := by rw [hadj]
    _ = Matrix.adjugate A * (A * A.conjTranspose) := by rw [Matrix.mul_assoc]
    _ = Matrix.adjugate A := by rw [hunit, Matrix.mul_one]
def specialScalar (U : SingleQubitSpecialUnitary) : Real :=
  ((U : SingleQubitMatrix) 0 0).re
def specialVector (U : SingleQubitSpecialUnitary) : Fin 3 → Real :=
  ![-((U : SingleQubitMatrix) 0 1).im,
    -((U : SingleQubitMatrix) 0 1).re,
    -((U : SingleQubitMatrix) 0 0).im]
theorem special_matrix_lower_entries (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix) 1 1 = star ((U : SingleQubitMatrix) 0 0) ∧
      (U : SingleQubitMatrix) 1 0 = -star ((U : SingleQubitMatrix) 0 1) := by
  have h := special_conjTranspose_eq_adjugate U
  constructor
  · have h00 := congrFun (congrFun h 0) 0
    simpa [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] using h00.symm
  · have h01 := congrFun (congrFun h 0) 1
    have h01' := congrArg star h01
    simpa [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] using h01'
theorem special_coordinate_matrix (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix) = su2Matrix (specialScalar U) (specialVector U) := by
  rcases special_matrix_lower_entries U with ⟨h11, h10⟩
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · change (U : SingleQubitMatrix) 1 0 = _
    rw [h10]
    apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · change (U : SingleQubitMatrix) 1 1 = _
    rw [h11]
    apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
theorem special_coordinate_norm (U : SingleQubitSpecialUnitary) :
    specialScalar U ^ 2 + specialVector U ⬝ᵥ specialVector U = 1 := by
  have hdet : (su2Matrix (specialScalar U) (specialVector U)).det = 1 := by
    rw [← special_coordinate_matrix U]
    exact U.2
  rw [su2Matrix_det_formula] at hdet
  exact_mod_cast hdet
def alternatingWordMap (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) : Fin 3 → Real :=
  alternatingWordVector axis axis' (p 0) (p 1) (p 2)
theorem alternatingWordMap_contDiff (axis axis' : UnitBlochAxis) :
    ContDiff Real ⊤ (alternatingWordMap axis axis') := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    simp [alternatingWordMap, alternatingWordVector, alternatingWordFirstScalar,
      alternatingWordFirstVector, blochVector, blochDot, cross_apply] <;>
    fun_prop
def alternatingWordBase : Fin 3 → Real := ![0, Real.pi / 4, 0]
def alternatingWordCoeffA (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  (Real.cos x * Real.cos y - Real.sin x * Real.sin y * blochDot axis axis') *
      Real.sin z +
    Real.cos z * Real.cos y * Real.sin x -
    Real.sin z * Real.sin x * Real.sin y * blochDot axis axis'
def alternatingWordCoeffB (_axis _axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  Real.cos z * Real.cos x * Real.sin y + Real.sin z * Real.sin x * Real.sin y
def alternatingWordCoeffCross (_axis _axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  Real.cos z * Real.sin x * Real.sin y - Real.sin z * Real.cos x * Real.sin y
theorem smul_cross_smul (r s : Real) (v w : Fin 3 → Real) :
    (r • v) ⨯₃ (s • w) = (r * s) • (v ⨯₃ w) := by
  ext i
  fin_cases i <;> simp [cross_apply, smul_eq_mul] <;> ring
theorem add_cross (u v w : Fin 3 → Real) :
    (u + v) ⨯₃ w = u ⨯₃ w + v ⨯₃ w := by
  ext i
  fin_cases i <;> simp [cross_apply]
theorem blochCross_cross_blochVector (axis axis' : UnitBlochAxis) :
    (blochVector axis ⨯₃ blochVector axis') ⨯₃ blochVector axis =
      blochVector axis' - blochDot axis axis' • blochVector axis := by
  rw [cross_cross_eq_smul_sub_smul]
  simp [blochVector_dot, blochDot]
  ring
theorem alternatingWordMap_formula (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) :
    alternatingWordMap axis axis' p =
      alternatingWordCoeffA axis axis' p • blochVector axis +
        alternatingWordCoeffB axis axis' p • blochVector axis' +
        alternatingWordCoeffCross axis axis' p •
          (blochVector axis ⨯₃ blochVector axis') := by
  simp only [alternatingWordMap, alternatingWordVector, alternatingWordFirstScalar,
    alternatingWordFirstVector, alternatingWordCoeffA, alternatingWordCoeffB,
    alternatingWordCoeffCross, smul_cross_smul, smul_smul]
  rw [add_cross, add_cross]
  rw [smul_cross_smul, smul_cross_smul, smul_cross_smul]
  rw [← cross_anticomm (blochVector axis) (blochVector axis')]
  rw [cross_self]
  rw [blochCross_cross_blochVector]
  module
def wordParameterProjection (i : Fin 3) : (Fin 3 → Real) →L[Real] Real :=
  ContinuousLinearMap.proj i
theorem hasFDerivAt_sin_parameter (i : Fin 3) (p : Fin 3 → Real) :
    HasFDerivAt (fun q : Fin 3 → Real => Real.sin (q i))
      (Real.cos (p i) • wordParameterProjection i) p := by
  have hproj : HasFDerivAt (fun q : Fin 3 → Real => q i) (wordParameterProjection i) p := by
    simpa [wordParameterProjection] using (hasFDerivAt_apply i p)
  exact hproj.sin
theorem hasFDerivAt_cos_parameter (i : Fin 3) (p : Fin 3 → Real) :
    HasFDerivAt (fun q : Fin 3 → Real => Real.cos (q i))
      (-Real.sin (p i) • wordParameterProjection i) p := by
  have hproj : HasFDerivAt (fun q : Fin 3 → Real => q i) (wordParameterProjection i) p := by
    simpa [wordParameterProjection] using (hasFDerivAt_apply i p)
  exact hproj.cos
theorem alternatingWordCoeffA_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffA axis axis')
      (Real.cos (Real.pi / 4) • wordParameterProjection 0 +
        Real.cos (Real.pi / 4) • wordParameterProjection 2)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hcy := hasFDerivAt_cos_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have hr := (hcx.mul hcy).sub (((hsx.mul hsy).mul_const (blochDot axis axis')))
  have h := (hr.mul hsz).add ((hcz.mul hcy).mul hsx) |>.sub
    ((((hsz.mul hsx).mul hsy).mul_const (blochDot axis axis')))
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection, ContinuousLinearMap.smul_apply] <;> ring
theorem alternatingWordCoeffB_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffB axis axis')
      (Real.cos (Real.pi / 4) • wordParameterProjection 1)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have h := ((hcz.mul hcx).mul hsy).add ((hsz.mul hsx).mul hsy)
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection, ContinuousLinearMap.smul_apply]
theorem alternatingWordCoeffCross_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffCross axis axis')
      (Real.sin (Real.pi / 4) • wordParameterProjection 0 -
        Real.sin (Real.pi / 4) • wordParameterProjection 2)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have h := ((hcz.mul hsx).mul hsy).sub ((hsz.mul hcx).mul hsy)
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection]
def alternatingWordDerivative (axis axis' : UnitBlochAxis) :
    (Fin 3 → Real) →ₗ[Real] Fin 3 → Real where
  toFun := fun h =>
    (Real.cos (Real.pi / 4) * (h 0 + h 2)) • blochVector axis +
      (Real.cos (Real.pi / 4) * h 1) • blochVector axis' +
      (Real.sin (Real.pi / 4) * (h 0 - h 2)) •
        (blochVector axis ⨯₃ blochVector axis')
  map_add' := by
    intro h k
    ext i
    simp [smul_eq_mul]
    ring
  map_smul' := by
    intro c h
    ext i
    simp [smul_eq_mul]
    ring
def alternatingWordDerivativeCLM (axis axis' : UnitBlochAxis) :
    (Fin 3 → Real) →L[Real] Fin 3 → Real :=
  ⟨alternatingWordDerivative axis axis',
    (alternatingWordDerivative axis axis').continuous_of_finiteDimensional⟩
theorem alternatingWordMap_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordMap axis axis')
      (alternatingWordDerivativeCLM axis axis') alternatingWordBase := by
  have hA := alternatingWordCoeffA_hasFDerivAt axis axis'
  have hB := alternatingWordCoeffB_hasFDerivAt axis axis'
  have hC := alternatingWordCoeffCross_hasFDerivAt axis axis'
  have h := (hA.smul_const (blochVector axis)).add
    ((hB.smul_const (blochVector axis')).add
      (hC.smul_const (blochVector axis ⨯₃ blochVector axis')))
  convert h using 1 <;> try rfl
  · funext p
    rw [alternatingWordMap_formula]
    simp only [Pi.add_apply]
    abel
  · ext q i
    simp [alternatingWordDerivativeCLM, alternatingWordDerivative,
      wordParameterProjection, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul] <;> ring
theorem blochCross_dot_self (axis axis' : UnitBlochAxis) :
    (blochVector axis ⨯₃ blochVector axis') ⬝ᵥ
      (blochVector axis ⨯₃ blochVector axis') = blochCrossSq axis axis' := by
  simp [blochCrossSq, blochVector, cross_apply]
  ring
theorem alternatingWordDerivative_injective (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    Function.Injective (alternatingWordDerivative axis axis') := by
  intro h k heq
  apply sub_eq_zero.mp
  let u : Fin 3 → Real := h - k
  have hzero : alternatingWordDerivative axis axis' u = 0 := by
    dsimp [u]
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  have hcross := congrArg (fun q =>
    (blochVector axis ⨯₃ blochVector axis') ⬝ᵥ q) hzero
  have haxis := congrArg (fun q => blochVector axis ⬝ᵥ q) hzero
  have haxis' := congrArg (fun q => blochVector axis' ⬝ᵥ q) hzero
  have hcross' :
      Real.sin (Real.pi / 4) * (u 0 - u 2) * blochCrossSq axis axis' = 0 := by
    simpa [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
      dotProduct_comm, blochCross_dot_self, smul_eq_mul] using hcross
  have hsin : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    positivity
  have hdiff : u 0 - u 2 = 0 := by
    have hprod : Real.sin (Real.pi / 4) * (u 0 - u 2) = 0 :=
      (mul_eq_zero.mp hcross').resolve_right (ne_of_gt hnonparallel)
    exact (mul_eq_zero.mp hprod).resolve_left hsin
  have hu2 : u 2 = u 0 := (sub_eq_zero.mp hdiff).symm
  have ha :
      (2 * Real.cos (Real.pi / 4) * u 0) +
        (Real.cos (Real.pi / 4) * u 1) * blochDot axis axis' = 0 := by
    convert haxis using 1 <;>
      simp [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
        blochVector_dot_self, blochVector_dot, smul_eq_mul, hu2] <;>
      ring
  have hb :
      (2 * Real.cos (Real.pi / 4) * u 0) * blochDot axis axis' +
        (Real.cos (Real.pi / 4) * u 1) = 0 := by
    convert haxis' using 1 <;>
      simp [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
        blochVector_dot_self, blochVector_dot, blochDot, smul_eq_mul, hu2] <;>
      ring
  have hA :
      (2 * Real.cos (Real.pi / 4) * u 0) *
        (1 - blochDot axis axis' ^ 2) = 0 := by
    linear_combination ha - blochDot axis axis' * hb
  have hA0 : 2 * Real.cos (Real.pi / 4) * u 0 = 0 := by
    apply (mul_eq_zero.mp hA).resolve_right
    rw [← blochCrossSq_eq_one_sub_blochDot_sq]
    exact ne_of_gt hnonparallel
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have hu0 : u 0 = 0 := by
    rcases mul_eq_zero.mp hA0 with hleft | hu0
    · exfalso
      rcases mul_eq_zero.mp hleft with htwo | hcos0
      · norm_num at htwo
      · exact hcos hcos0
    · exact hu0
  have hu1 : u 1 = 0 := by
    rw [hu0] at hb
    have hcu : Real.cos (Real.pi / 4) * u 1 = 0 := by
      convert hb using 1 <;> ring
    exact (mul_eq_zero.mp hcu).resolve_left hcos
  have hu : u = 0 := by
    ext i
    fin_cases i <;> simp [u, hu0, hu1, hu2]
  simpa [u] using hu
noncomputable def alternatingWordDerivativeEquiv (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    (Fin 3 → Real) ≃L[Real] Fin 3 → Real := by
  apply ContinuousLinearEquiv.ofBijective (alternatingWordDerivativeCLM axis axis')
  · exact LinearMap.ker_eq_bot.mpr (alternatingWordDerivative_injective axis axis' hnonparallel)
  · apply LinearMap.range_eq_top.mpr
    exact LinearMap.surjective_of_injective
      (alternatingWordDerivative_injective axis axis' hnonparallel)
noncomputable def alternatingWordLocalHomeomorph (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    OpenPartialHomeomorph (Fin 3 → Real) (Fin 3 → Real) := by
  have hcont : ContDiffAt Real ⊤ (alternatingWordMap axis axis') alternatingWordBase :=
    (alternatingWordMap_contDiff axis axis').contDiffAt
  refine hcont.toOpenPartialHomeomorph (alternatingWordMap axis axis')
    (f' := alternatingWordDerivativeEquiv axis axis' hnonparallel) ?_ (by simp)
  exact alternatingWordMap_hasFDerivAt axis axis'
def alternatingWordPositiveSet (axis axis' : UnitBlochAxis) : Set (Fin 3 → Real) :=
  {p | 0 < alternatingWordScalar axis axis' (p 0) (p 1) (p 2)}
theorem isOpen_alternatingWordPositiveSet (axis axis' : UnitBlochAxis) :
    IsOpen (alternatingWordPositiveSet axis axis') := by
  apply isOpen_lt continuous_const
  simp only [alternatingWordScalar,
    alternatingWordFirstScalar, alternatingWordFirstVector]
  fun_prop
noncomputable def alternatingWordPositiveLocalHomeomorph (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    OpenPartialHomeomorph (Fin 3 → Real) (Fin 3 → Real) :=
  (alternatingWordLocalHomeomorph axis axis' hnonparallel).restrOpen
    (alternatingWordPositiveSet axis axis') (isOpen_alternatingWordPositiveSet axis axis')
theorem vector_dot_self_nonneg (v : Fin 3 → Real) : 0 ≤ v ⬝ᵥ v := by
  simpa using (dotProduct_star_self_nonneg v)
def standardBlochAxis : UnitBlochAxis :=
  ⟨0, 0, 1, by norm_num⟩
noncomputable def normalizedBlochAxis (v : Fin 3 → Real) (hnonzero : v ⬝ᵥ v ≠ 0) :
    UnitBlochAxis := by
  let m : Real := Real.sqrt (v ⬝ᵥ v)
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hpos : 0 < m :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hnonzero))
  refine ⟨v 0 / m, v 1 / m, v 2 / m, ?_⟩
  rw [div_pow, div_pow, div_pow]
  have hsq : m ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hnonneg
  field_simp
  rw [hsq]
  simp only [Matrix.vec3_dotProduct]
  ring
theorem sqrt_smul_blochVector_normalizedBlochAxis (v : Fin 3 → Real)
    (hnonzero : v ⬝ᵥ v ≠ 0) :
    Real.sqrt (v ⬝ᵥ v) • blochVector (normalizedBlochAxis v hnonzero) = v := by
  let m : Real := Real.sqrt (v ⬝ᵥ v)
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hpos : 0 < m :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hnonzero))
  ext i
  fin_cases i <;> simp [normalizedBlochAxis, blochVector]
  all_goals
    field_simp
theorem axisCircleRealSU_continuous (axis : UnitBlochAxis) :
    Continuous (axisCircleRealSU axis) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : Real => axisCircle axis (x : AddCircle (2 * Real.pi)))
  exact (axisCircle_continuous axis).comp (AddCircle.continuous_mk' _)
theorem exists_axisCircleRealSU_eq (U : SingleQubitSpecialUnitary) :
    ∃ axis : UnitBlochAxis, ∃ theta : Real, axisCircleRealSU axis theta = U := by
  let r := specialScalar U
  let v := specialVector U
  have hnorm : r ^ 2 + v ⬝ᵥ v = 1 := by
    simpa [r, v] using special_coordinate_norm U
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hsqle : r ^ 2 ≤ 1 := by
    nlinarith
  have hrabs : |r| ≤ 1 := (sq_le_one_iff_abs_le_one r).mp hsqle
  have hrneg : -1 ≤ r := (abs_le.mp hrabs).1
  have hrpos : r ≤ 1 := (abs_le.mp hrabs).2
  let theta := Real.arccos r
  have hcos : Real.cos theta = r := by
    dsimp [theta]
    exact Real.cos_arccos hrneg hrpos
  have hsin : Real.sin theta = Real.sqrt (v ⬝ᵥ v) := by
    dsimp [theta]
    rw [Real.sin_arccos]
    congr 1
    nlinarith
  by_cases hvzero : v ⬝ᵥ v = 0
  · have hv : v = 0 := dotProduct_self_eq_zero.mp hvzero
    refine ⟨standardBlochAxis, theta, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (axisCircleRealSU standardBlochAxis theta : SingleQubitMatrix) =
      (U : SingleQubitMatrix)
    rw [axisCircleRealSU_matrix, special_coordinate_matrix U]
    change su2Matrix (Real.cos theta)
      (Real.sin theta • blochVector standardBlochAxis) = su2Matrix r v
    rw [hcos, hsin, hv]
    simp
  · let axis := normalizedBlochAxis v hvzero
    have hscale : Real.sqrt (v ⬝ᵥ v) • blochVector axis = v := by
      simpa [axis] using sqrt_smul_blochVector_normalizedBlochAxis v hvzero
    refine ⟨axis, theta, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (axisCircleRealSU axis theta : SingleQubitMatrix) =
      (U : SingleQubitMatrix)
    rw [axisCircleRealSU_matrix, special_coordinate_matrix U]
    change su2Matrix (Real.cos theta)
      (Real.sin theta • blochVector axis) = su2Matrix r v
    rw [hcos, hsin, hscale]
@[simp] theorem axisCircleRealSU_zero (axis : UnitBlochAxis) :
    axisCircleRealSU axis 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (axisCircle axis (0 : AddCircle (2 * Real.pi)) : SingleQubitMatrix) = 1
  simp
noncomputable def axisCircleRealSUPath (axis : UnitBlochAxis) (theta : Real) :
    Path 1 (axisCircleRealSU axis theta) where
  toFun := fun s : unitInterval => axisCircleRealSU axis ((s : Real) * theta)
  continuous_toFun :=
    (axisCircleRealSU_continuous axis).comp (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simp
theorem nonempty_specialUnitaryPath (U : SingleQubitSpecialUnitary) :
    Nonempty (Path 1 U) := by
  rcases exists_axisCircleRealSU_eq U with ⟨axis, theta, haxis⟩
  exact ⟨haxis ▸ axisCircleRealSUPath axis theta⟩
noncomputable def specialUnitaryPath (U : SingleQubitSpecialUnitary) : Path 1 U :=
  Classical.choice (nonempty_specialUnitaryPath U)
end Distillation
end QEC


