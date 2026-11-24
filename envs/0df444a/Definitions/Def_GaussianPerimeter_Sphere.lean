-- Prove2me | Definitions.Def_GaussianPerimeter_Sphere
-- name    : GaussianPerimeter_Sphere
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:05:59.029475+00:00
-- url     : https://prove2.me/theorems/73e56bc1-74fe-4099-81ee-04991dc93749
-- title:
--   Sphere
-- statement:
--   Definitions and structural lemmas for Sphere, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Sphere.lean

module
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace
namespace GaussianPerimeter
local notation "UnitSphere" E => Metric.sphere (0 : E) 1
section Sphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
noncomputable def uniformSphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (UnitSphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ univ)⁻¹ • σ
instance [Nontrivial E] : IsProbabilityMeasure (uniformSphere E) where
  measure_univ := by
    rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (fun h => (Measure.toSphere_ne_zero (volume : Measure E)) (Measure.measure_univ_eq_zero.mp h))
      (measure_ne_top _ _)
end Sphere
section Cone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
@[expose] def capCone (v : E) (t : ℝ) : Set E :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ ≤ ⟪v, x⟫}
end Cone
section Isometries
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
end Isometries
end GaussianPerimeter


