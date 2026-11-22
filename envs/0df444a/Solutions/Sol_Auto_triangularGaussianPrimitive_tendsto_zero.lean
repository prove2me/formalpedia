-- Prove2me | solution 1 for Auto.triangularGaussianPrimitive_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:43:40.270671+00:00
-- url     : https://prove2.me/submissions/cf7a9eab-378a-4fdf-9650-b1e2e2666e53

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularCutoffProfile_tendsto
public import Theorems.Thm_Auto_triangularGaussianPrimitive_eq_profile

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun s : ℝ => t ^ 2 / (2 * c * s)) (𝓝[>] 0) atTop := by
    have h := Tendsto.const_mul_atTop (show 0 < t ^ 2 / (2 * c) by positivity)
      (tendsto_inv_nhdsGT_zero : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] 0) atTop)
    convert h using 1
    ext s; simp [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm, mul_left_comm]
  have h := (triangularCutoffProfile_tendsto.comp hu).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  simpa [triangularGaussianPrimitive_eq_profile] using h
end Auto
