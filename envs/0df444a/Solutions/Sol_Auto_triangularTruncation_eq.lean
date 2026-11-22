-- Prove2me | solution 1 for Auto.triangularTruncation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:16.403798+00:00
-- url     : https://prove2.me/submissions/b99a2c08-6c5b-4574-8fc5-451abc412c70

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_integral_symmetrize
public import Theorems.Thm_Auto_triangular_truncation_integrable

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    triangularTruncation H F G ε = (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.2| then
      triangularOddQuotient H F G q else 0 := by
  rw [triangularTruncation, triangular_integral_symmetrize (triangular_truncation_integrable H F G
      hε)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [abs_neg, Complex.ofReal_neg]
  split_ifs <;> simp [triangularOddQuotient]; ring
end Auto
