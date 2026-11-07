-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
-- name    : QEC_Coding_ExpanderCodes_QuaternionMatrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:31:25.429743+00:00
-- url     : https://prove2.me/theorems/fafabfc1-7252-4bd0-b5b8-a9bcbc0fe700
-- title:
--   Quaternion Matrix
-- statement:
--   Definitions and structural lemmas for Quaternion Matrix, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionMatrix.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix
def matrixCoordinates (r y : K) (q : Model (r ^ 2) y) : Matrix (Fin 2) (Fin 2) K :=
  !![q.re + q.imI * r, (q.imJ + q.imK * r) * (1 + y);
     q.imJ - q.imK * r, q.re - q.imI * r]
def matrixHom (r y : K) : Model (r ^ 2) y →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixCoordinates r y
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixCoordinates]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixCoordinates]
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixCoordinates] <;> ring
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixCoordinates, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
def quaternionCoordinates (r y : K) (M : Matrix (Fin 2) (Fin 2) K) : Model (r ^ 2) y :=
  ⟨(M 0 0 + M 1 1) / 2,
   (M 0 0 - M 1 1) / (2 * r),
   (M 0 1 / (1 + y) + M 1 0) / 2,
   (M 0 1 / (1 + y) - M 1 0) / (2 * r)⟩
def matrixEquiv (r y : K) (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Model (r ^ 2) y ≃+* Matrix (Fin 2) (Fin 2) K where
  __ := matrixHom r y
  invFun := quaternionCoordinates r y
  left_inv q := by
    ext <;> simp [matrixHom, matrixCoordinates, quaternionCoordinates] <;> field_simp <;> ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixHom, matrixCoordinates, quaternionCoordinates] <;> field_simp <;> ring
theorem center_map_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨x, rfl⟩ := e.surjective h
    change e x * e g = e g * e x
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hg x)
  · intro hh
    refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hh (e x)
def projectiveMatrixEquiv (r y : K) (hR : r ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    ProjectiveGroup (r ^ 2) y ≃* Matrix.ProjGenLinGroup (Fin 2) K :=
  QuotientGroup.congr _ _
    (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv)
    (center_map_eq _)
def matrixEquivOfRoot (epsilon r y : K) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Model epsilon y ≃+* Matrix (Fin 2) (Fin 2) K := by
  subst epsilon
  exact matrixEquiv r y hR hOne hTwo
def projectiveMatrixEquivOfRoot (epsilon r y : K) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    ProjectiveGroup epsilon y ≃* Matrix.ProjGenLinGroup (Fin 2) K := by
  subst epsilon
  exact projectiveMatrixEquiv r y hR hOne hTwo
end QEC.Coding.ExpanderCodes.QuaternionGenerators


