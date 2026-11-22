-- Prove2me | solution 1 for Auto.triangular_Kern_mul_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:47:41.8334+00:00
-- url     : https://prove2.me/submissions/9301e623-94ef-46e8-854f-a291a59232d3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_Kern_tendsto

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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => t * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝
      triangularKernelCoefficient) := by
  convert (triangular_Kern_tendsto ht).const_mul t using 1
  congr 1
  unfold triangularKernelCoefficient; field_simp
end Auto
