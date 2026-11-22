-- Prove2me | solution 1 for Auto.triangular_Kern_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:46:22.984654+00:00
-- url     : https://prove2.me/submissions/4c57fb07-5305-43dd-a34e-4aa1188b7d7c

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_Kern_eq_primitive
public import Theorems.Thm_Auto_triangularGaussianPrimitive_tendsto_top
public import Theorems.Thm_Auto_triangularGaussianPrimitive_tendsto_zero

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
    Tendsto (fun n : ℕ => Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝 (2 / ((63 / 20 : ℝ) *
      Real.sqrt (2 * Real.pi * (63 / 20)) * t))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop := (triangularGaussianPrimitive_tendsto_top (by norm_num : (0 : ℝ) < 63 / 20) t).comp hn
  have hzero := (triangularGaussianPrimitive_tendsto_zero (by norm_num : (0 : ℝ) < 63 / 20) ht).comp
    (tendsto_inv_atTop_nhdsGT_zero.comp hn)
  have h := htop.sub hzero
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact (triangular_Kern_eq_primitive (inv_pos.mpr hn0)
    ((inv_le_one₀ hn0).mpr hn1 |>.trans hn1) ht).symm
end Auto
