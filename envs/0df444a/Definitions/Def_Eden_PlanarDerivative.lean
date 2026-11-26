-- Prove2me | Definitions.Def_Eden_PlanarDerivative
-- name    : Eden_PlanarDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:21:46.59352+00:00
-- url     : https://prove2.me/theorems/e13e0020-9013-5cae-858e-835db90ffc08
-- title:
--   Planar Derivative
-- statement:
--   Definitions and structural lemmas for Planar Derivative, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarDerivative.lean

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


set_option autoImplicit true
noncomputable section
namespace Eden
def planarEvolution (Ω t : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[planarX Ω t (p 0) (p 1), planarY Ω t (p 0) (p 1)]
@[simp] theorem planarEvolution_zero_time (Ω : ℝ) (p : PlanarSpace) :
    planarEvolution Ω 0 p = p := by
  ext i
  fin_cases i <;> simp [planarEvolution]
def rotatePlane (a b : ℝ) (v : PlanarSpace) : PlanarSpace :=
  !₂[a * v 0 - b * v 1, b * v 0 + a * v 1]
theorem rotatePlane_inverse {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    rotatePlane a (-b) (rotatePlane a b v) = v := by
  have h₀ := congrArg (fun r : ℝ => r * v 0) hab
  have h₁ := congrArg (fun r : ℝ => r * v 1) hab
  ext i
  fin_cases i <;> simp [rotatePlane] <;> nlinarith only [h₀, h₁]
theorem norm_rotatePlane {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    ‖rotatePlane a b v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [rotatePlane]
  nlinarith [congrArg (fun r : ℝ => r * ((v 0) ^ 2 + (v 1) ^ 2)) hab]
def planeRotation (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace where
  toFun := rotatePlane a b
  invFun := rotatePlane a (-b)
  left_inv := rotatePlane_inverse hab
  right_inv := by
    have h : a ^ 2 + (-b) ^ 2 = 1 := by simpa using hab
    intro v
    simpa using rotatePlane_inverse h v
  map_add' := by intro v w; ext i; fin_cases i <;> simp [rotatePlane] <;> ring
  map_smul' := by intro r v; ext i; fin_cases i <;> simp [rotatePlane, smul_eq_mul] <;> ring
  norm_map' := norm_rotatePlane hab
@[simp] theorem planeRotation_apply (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (v : PlanarSpace) :
    planeRotation a b hab v = rotatePlane a b v := rfl
def planarRadialFrame (p : PlanarSpace) : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  planeRotation (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (radialCos_sq_add_radialSin_sq _ _)
def planarAngularRotation (Ω t : ℝ) : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  planeRotation (Real.cos (Ω * t)) (Real.sin (Ω * t))
    (by nlinarith [Real.sin_sq_add_cos_sq (Ω * t)])
def planarDiagonal (d : PlanarSpace) : PlanarSpace →ₗ[ℝ] PlanarSpace where
  toFun v := WithLp.toLp 2 (fun i => d i * v i)
  map_add' := by intro v w; ext i; simp [mul_add]
  map_smul' := by intro r v; ext i; simp [smul_eq_mul]; ring
def planarFactors (t : ℝ) (p : PlanarSpace) : PlanarSpace :=
  !₂[radialAmplitude t (p 0 ^ 2 + p 1 ^ 2), planarAmplitude t (p 0 ^ 2 + p 1 ^ 2)]
end Eden


