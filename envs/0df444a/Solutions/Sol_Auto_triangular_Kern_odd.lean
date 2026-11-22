-- Prove2me | solution 1 for Auto.triangular_Kern_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:57:31.556878+00:00
-- url     : https://prove2.me/submissions/3c2db574-59a3-49e3-8e02-00633d07d53e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_Kern_eq
public import Theorems.Thm_Auto_triangular_gaussian_third

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
    Kern 3 a b (-t) = -Kern 3 a b t := by
  rw [Kern_eq, Kern_eq, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs; rw [Set.uIcc_of_le hab] at hs
  have hp : 0 < (63 / 20 : ℝ) * s := mul_pos (by norm_num) (ha.trans_le hs.1)
  simp only [kernIntegrand, triangular_gaussian_third hp, gaussian, neg_sq]; ring
end Auto
