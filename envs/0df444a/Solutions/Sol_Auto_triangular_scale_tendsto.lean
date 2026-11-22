-- Prove2me | solution 1 for Auto.triangular_scale_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:52:42.047448+00:00
-- url     : https://prove2.me/submissions/5057033b-6935-40c6-aefb-20fcc1e12876

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_cancelled_scale_tendsto
public import Theorems.Thm_Auto_triangular_scale_eq

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
    Tendsto (fun n : ℕ => ∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern
      3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℂ)) atTop (𝓝 ((triangularKernelCoefficient : ℂ) *
      triangularPV H F G)) := by
  apply (triangular_cancelled_scale_tendsto H F G).congr
  intro n
  apply (triangular_scale_eq H F G (by positivity) _).symm
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact ((inv_le_one₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr hn).trans hn
end Auto
