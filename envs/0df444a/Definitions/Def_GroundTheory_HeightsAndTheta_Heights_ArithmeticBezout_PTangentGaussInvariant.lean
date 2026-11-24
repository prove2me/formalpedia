-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:19.516959+00:00
-- url     : https://prove2.me/theorems/436c91d3-21a4-4387-af1f-51a9c37106bc
-- title:
--   PTangent Gauss Invariant
-- statement:
--   Definitions and structural lemmas for PTangent Gauss Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
def unitMat {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap
theorem unitMat_mem {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  U.toMatrix_mem_unitaryGroup _ _
theorem unitMat_mul_symm {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U * unitMat U.symm = 1 := by
  rw [unitMat, unitMat, ← LinearMap.toMatrix_mul]
  have : U.toLinearMap * U.symm.toLinearMap = 1 := LinearMap.ext fun x => by simp
  rw [this, LinearMap.toMatrix_one]
theorem measurePreserving_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun r : Fin n → ℂ => r ᵥ* A) volume volume := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ with hf
  have hfun : (fun r : Fin n → ℂ => r ᵥ* A) = f := by
    funext r
    simp [hf, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hdet : LinearMap.det f = 1 := by
    have hd : ‖A.det‖ = 1 := by
      have h1 : A.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hA
      exact CStarRing.norm_of_mem_unitary h1
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hmeas : Measurable (fun r : Fin n → ℂ => r ᵥ* A) := by
    apply Continuous.measurable
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp
def matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i => π i ᵥ* unitMat U
theorem measurePreserving_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (matSub (m := m) U) volume volume :=
  volume_preserving_pi fun _ => measurePreserving_vecMul (unitMat_mem U)
theorem matSub_symm_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin m → Fin n → ℂ) :
    matSub U.symm (matSub U π) = π := by
  funext i
  simp [matSub, Matrix.vecMul_vecMul, unitMat_mul_symm]
def matSubEquiv {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := matSub U
  invFun := matSub U.symm
  left_inv := matSub_symm_matSub U
  right_inv π := by simpa using matSub_symm_matSub U.symm π
  measurable_toFun := (measurePreserving_matSub U).measurable
  measurable_invFun := (measurePreserving_matSub U.symm).measurable
end
end GroundTheory.Heights₂.Heights


