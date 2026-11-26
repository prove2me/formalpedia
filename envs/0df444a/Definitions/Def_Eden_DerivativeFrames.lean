-- Prove2me | Definitions.Def_Eden_DerivativeFrames
-- name    : Eden_DerivativeFrames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:15:52.031502+00:00
-- url     : https://prove2.me/theorems/6718e3e3-6be0-5056-90b3-b9cbf2c7d965
-- title:
--   Derivative Frames
-- statement:
--   Definitions and structural lemmas for Derivative Frames, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeFrames.lean

import Definitions.Def_Eden_CartesianDerivative
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_OrthogonalFrames
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
def radialCos (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 1 else x / Real.sqrt (x ^ 2 + y ^ 2)
def radialSin (x y : ℝ) : ℝ :=
  if x ^ 2 + y ^ 2 = 0 then 0 else y / Real.sqrt (x ^ 2 + y ^ 2)
theorem radialCos_sq_add_radialSin_sq (x y : ℝ) :
    radialCos x y ^ 2 + radialSin x y ^ 2 = 1 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · simp [radialCos, radialSin, h]
  have hr : 0 < Real.sqrt (x ^ 2 + y ^ 2) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm h))
  have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  simp only [radialCos, radialSin, if_neg h]
  field_simp [ne_of_gt hr]
  nlinarith
def radialFrame (p : PhaseSpace) : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace :=
  blockRotation (radialCos (p 0) (p 1)) (radialSin (p 0) (p 1))
    (radialCos (p 2) (p 3)) (radialSin (p 2) (p 3))
    (radialCos_sq_add_radialSin_sq _ _) (radialCos_sq_add_radialSin_sq _ _)
def angularRotation (t : ℝ) : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace :=
  blockRotation (Real.cos t) (Real.sin t)
    (Real.cos (Real.sqrt 2 * t)) (Real.sin (Real.sqrt 2 * t))
    (by nlinarith [Real.sin_sq_add_cos_sq t])
    (by nlinarith [Real.sin_sq_add_cos_sq (Real.sqrt 2 * t)])
end Eden


