-- Prove2me | solution 1 for Auto.triangular_scale_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:16.877058+00:00
-- url     : https://prove2.me/submissions/639d5a87-1dec-455c-a504-29f901430a80

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_snd_ne_zero
public import Theorems.Thm_Auto_triangular_integral_symmetrize
public import Theorems.Thm_Auto_triangular_Kern_odd
public import Theorems.Thm_Auto_triangular_scale_integrable

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b q.2 : ℂ)) = (2
      : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 * Kern 3 a b q.2 : ℝ) : ℂ)
          := by
  rw [triangular_integral_symmetrize (triangular_scale_integrable H F G ha hab)]
  congr 1
  apply integral_congr_ae
  filter_upwards [triangular_snd_ne_zero] with q hq
  simp only [triangular_Kern_odd ha hab, Complex.ofReal_neg, triangularOddQuotient,
    Complex.ofReal_mul]
  have hz : (q.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  field_simp; ring
end Auto
