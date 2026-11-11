-- Prove2me | Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
-- name    : QEC_Distillation_Universality_OneQubitPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:58:49.694301+00:00
-- url     : https://prove2.me/theorems/1dba1c0a-c72f-4900-a72c-05d7f272970d
-- title:
--   One Qubit Phase
-- statement:
--   Definitions and structural lemmas for One Qubit Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitPhase.lean

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
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
namespace OneQubitMagic
open Semantics Semantics.Qubit
def phaseAmplitude (theta : Real) : Complex :=
  Complex.exp ((theta : Complex) * Complex.I)
@[simp] theorem phaseAmplitude_zero : phaseAmplitude 0 = 1 := by
  simp [phaseAmplitude]
theorem phaseAmplitude_add (theta phi : Real) :
    phaseAmplitude (theta + phi) =
      phaseAmplitude theta * phaseAmplitude phi := by
  unfold phaseAmplitude
  rw [show (((theta + phi : Real) : Complex) * Complex.I) =
      (theta : Complex) * Complex.I + (phi : Complex) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_add _ _
@[simp] theorem phaseAmplitude_norm (theta : Real) :
    ‖phaseAmplitude theta‖ = 1 := by
  simpa [phaseAmplitude] using Complex.norm_exp_ofReal_mul_I theta
@[simp] theorem phaseAmplitude_mul_conj (theta : Real) :
    phaseAmplitude theta * star (phaseAmplitude theta) = 1 := by
  rw [Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, phaseAmplitude_norm]
  norm_num
def phaseState (theta : Real) : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (Real.sqrt 2 : Complex)⁻¹
    else (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta
@[simp] theorem phaseState_apply_zero (theta : Real) :
    phaseState theta 0 = (Real.sqrt 2 : Complex)⁻¹ := by
  simp [phaseState]
@[simp] theorem phaseState_apply_one (theta : Real) :
    phaseState theta 1 =
      (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta := by
  simp [phaseState]
theorem phaseState_inner_self (theta : Real) :
    inner Complex (phaseState theta) (phaseState theta) = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, phaseState_apply_zero,
    phaseState_apply_one, RCLike.inner_apply]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ +
        (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta *
          ((Real.sqrt 2 : Complex)⁻¹ * star (phaseAmplitude theta)) =
        (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ +
          ((Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) *
            (phaseAmplitude theta * star (phaseAmplitude theta)) := by
      ring
    _ = 2 * ((Real.sqrt 2 : Complex)⁻¹ *
          (Real.sqrt 2 : Complex)⁻¹) := by
      rw [phaseAmplitude_mul_conj]
      ring
    _ = 1 := by
      field_simp [hsqrt_ne]
      rw [pow_two, hsqrt_sq]
@[simp] theorem phaseState_norm (theta : Real) :
    ‖phaseState theta‖ = 1 := by
  have hinner := phaseState_inner_self theta
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖phaseState theta‖ ^ 2 = 1 := by
    have hsq_complex :
        ((‖phaseState theta‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg (phaseState theta)]
theorem phaseState_ne_zero (theta : Real) :
    phaseState theta ≠ 0 := by
  intro hzero
  have hnorm := phaseState_norm theta
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm
noncomputable def phaseStateDensity (theta : Real) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (phaseState theta) (phaseState_ne_zero theta)
@[simp] theorem phaseStateDensity_toOperator (theta : Real) :
    (phaseStateDensity theta).toOperator =
      (InnerProductSpace.rankOne Complex
        (phaseState theta) (phaseState theta)).toLinearMap := by
  rw [phaseStateDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [phaseState_inner_self]
  simp
def phaseShiftMatrix (theta : Real) : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, phaseAmplitude theta]
def phaseShiftOperator (theta : Real) : Operator QubitSpace :=
  Matrix.toEuclideanLin (phaseShiftMatrix theta)
@[simp] theorem phaseShiftOperator_apply_zero (theta : Real) (psi : QubitSpace) :
    phaseShiftOperator theta psi 0 = psi 0 := by
  simp [phaseShiftOperator, phaseShiftMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem phaseShiftOperator_apply_one (theta : Real) (psi : QubitSpace) :
    phaseShiftOperator theta psi 1 = phaseAmplitude theta * psi 1 := by
  simp [phaseShiftOperator, phaseShiftMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem phaseShiftOperator_zero :
    phaseShiftOperator 0 = (1 : Operator QubitSpace) := by
  ext psi b
  fin_cases b <;> simp
theorem phaseShiftOperator_add (theta phi : Real) :
    phaseShiftOperator theta * phaseShiftOperator phi =
      phaseShiftOperator (theta + phi) := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, phaseAmplitude_add] <;> ring
@[simp] theorem phaseShiftOperator_neg_mul (theta : Real) :
    phaseShiftOperator (-theta) * phaseShiftOperator theta = 1 := by
  rw [phaseShiftOperator_add]
  simp
@[simp] theorem phaseShiftOperator_mul_neg (theta : Real) :
    phaseShiftOperator theta * phaseShiftOperator (-theta) = 1 := by
  rw [phaseShiftOperator_add]
  simp
theorem phaseShiftOperator_map_inner (theta : Real)
    (x y : QubitSpace) :
    inner Complex (phaseShiftOperator theta x)
      (phaseShiftOperator theta y) = inner Complex x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, phaseShiftOperator_apply_zero,
    phaseShiftOperator_apply_one, RCLike.inner_apply, map_mul]
  calc
    y 0 * star (x 0) +
        phaseAmplitude theta * y 1 *
          (star (phaseAmplitude theta) * star (x 1)) =
      y 0 * star (x 0) +
        (phaseAmplitude theta * star (phaseAmplitude theta)) *
          (y 1 * star (x 1)) := by ring
    _ = y 0 * star (x 0) + y 1 * star (x 1) := by
      rw [phaseAmplitude_mul_conj]
      ring
def phaseShiftLinearEquiv (theta : Real) :
    QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk (phaseShiftOperator theta) (phaseShiftOperator (-theta))
    (fun psi => by
      change phaseShiftOperator (-theta) (phaseShiftOperator theta psi) = psi
      have h := LinearMap.congr_fun (phaseShiftOperator_neg_mul theta) psi
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h)
    (fun psi => by
      change phaseShiftOperator theta (phaseShiftOperator (-theta) psi) = psi
      have h := LinearMap.congr_fun (phaseShiftOperator_mul_neg theta) psi
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h)
def phaseShiftTransport (theta : Real) :
    UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseShiftLinearEquiv theta
  map_inner := phaseShiftOperator_map_inner theta
end OneQubitMagic
end Distillation
end QEC


