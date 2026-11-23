-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
-- name    : ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:41.215638+00:00
-- url     : https://prove2.me/theorems/a443bdb3-07c5-466c-972c-c36be2fd50fd
-- title:
--   Measure Preserving Sphere Map
-- statement:
--   Definitions and structural lemmas for Measure Preserving Sphere Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/MeasurePreservingSphereMap.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
def sphereMap {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (z : UnitSphereC n) : UnitSphereC n :=
  ⟨U z, by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
           exact mem_sphere_zero_iff_norm.mp z.2⟩
def rotCL {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (innerSL ℂ u).smulRight u + t • (ContinuousLinearMap.id ℂ _ - (innerSL ℂ u).smulRight u)
theorem rotCL_apply {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) (t : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    rotCL u t x = inner ℂ u x • u + t • (x - inner ℂ u x • u) := by
  simp [rotCL]
theorem norm_rotCL {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    (x : EuclideanSpace ℂ (Fin n)) : ‖rotCL u t x‖ = ‖x‖ := by
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have horth : inner ℂ u (x - inner ℂ u x • u) = 0 := by
    rw [inner_sub_right, inner_smul_right, huu, mul_one, sub_self]
  have h1 : inner ℂ (inner ℂ u x • u) (t • (x - inner ℂ u x • u)) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]; simp
  have h2 : inner ℂ (inner ℂ u x • u) (x - inner ℂ u x • u) = 0 := by
    rw [inner_smul_left, horth]; simp
  have hx : x = inner ℂ u x • u + (x - inner ℂ u x • u) := by abel
  have key : ‖rotCL u t x‖ * ‖rotCL u t x‖ = ‖x‖ * ‖x‖ := by
    rw [rotCL_apply, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1,
      norm_smul t (x - inner ℂ u x • u), ht, one_mul]
    conv_rhs => rw [hx, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp key
def rotIso {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} {t : ℂ} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((rotCL u t : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
      norm_map' := norm_rotCL hu ht } rfl
def rotS {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : ‖u‖ = 1) (θ : ℝ) :
    UnitSphereC n → UnitSphereC n :=
  sphereMap (rotIso hu (t := circleMap 0 1 θ) (by simp [norm_circleMap_zero]))
end ReciprocityTheory.MultiplicativeHeights


