-- Prove2me | solution 1 for Auto.triangular_scale_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:44:44.827809+00:00
-- url     : https://prove2.me/submissions/83e307e4-2fed-4efc-b073-175785cb9b78

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_Kern
public import Theorems.Thm_Auto_abs_Kern_le
public import Theorems.Thm_Auto_triangular_product_integrable

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
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b
      q.2 : ℂ)) := by
  obtain ⟨C, hC⟩ := abs_Kern_le 3 ha hab
  apply (triangular_product_integrable H F G).mul_bdd (c := C)
  · exact (Complex.continuous_ofReal.comp ((continuous_Kern 3 ha hab).comp
      continuous_snd)).aestronglyMeasurable
  · filter_upwards [] with q
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hC q.2
end Auto
