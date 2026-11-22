-- Prove2me | solution 1 for Auto.triangular_Kern_mul_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:44.4391+00:00
-- url     : https://prove2.me/submissions/9e2a7a3d-ca9c-49db-89a5-f66e5597dee3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_Kern_eq_primitive
public import Theorems.Thm_Auto_triangularCutoffProfile_bound
public import Theorems.Thm_Auto_triangularGaussianPrimitive_eq_profile
public import Theorems.Thm_Auto_triangularKernelCoefficient_pos

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
theorem _root_.solution {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    |t * Kern 3 a b t| ≤ 6 * triangularKernelCoefficient := by
  by_cases ht : t = 0
  · simp only [ht, zero_mul, abs_zero]
    positivity [triangularKernelCoefficient_pos]
  have he : t * Kern 3 a b t = triangularKernelCoefficient *
      (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)) -
        triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a))) := by
    rw [triangular_Kern_eq_primitive ha hab ht,
      triangularGaussianPrimitive_eq_profile, triangularGaussianPrimitive_eq_profile]
    unfold triangularKernelCoefficient; field_simp
  rw [he, abs_mul, abs_of_pos triangularKernelCoefficient_pos]
  have hb := triangularCutoffProfile_bound
    (show 0 ≤ t ^ 2 / (2 * (63 / 20) * b) by have := ha.trans_le hab; positivity)
  have ha' := triangularCutoffProfile_bound
    (show 0 ≤ t ^ 2 / (2 * (63 / 20) * a) by positivity)
  have hd := abs_sub_le (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)))
    0 (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a)))
  simp only [sub_zero, zero_sub, abs_neg] at hd
  have hle : |triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)) -
      triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a))| ≤ 6 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle triangularKernelCoefficient_pos.le]
end Auto
