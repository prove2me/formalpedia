-- Prove2me | solution 1 for Auto.triangular_cancelled_scale_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:51:11.640922+00:00
-- url     : https://prove2.me/submissions/d7982ad8-6eb2-4e3f-9743-30d6c9987aa9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_kernel_pairing_tendsto
public import Theorems.Thm_Auto_triangular_snd_ne_zero

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun n : ℕ => (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 *
      Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℝ) : ℂ)) atTop (𝓝 ((triangularKernelCoefficient :
      ℂ) * triangularPV H F G)) := by
  have h := (triangular_kernel_pairing_tendsto
    (triangularOddQuotient_integrable H F G) measurable_snd triangular_snd_ne_zero).const_mul
      (2 : ℂ)⁻¹
  simpa [triangularPV, mul_left_comm] using h
end Auto
