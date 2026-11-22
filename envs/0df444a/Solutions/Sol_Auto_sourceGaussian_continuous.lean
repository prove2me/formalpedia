-- Prove2me | solution 1 for Auto.sourceGaussian_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:55:00.616418+00:00
-- url     : https://prove2.me/submissions/8e8e1862-a6df-4ee8-bec4-39298d1926cc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_Kern

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
theorem _root_.solution (F : Fin 3 → ℝ × ℝ → ℂ)
    (hF : ∀ v, Continuous (F v)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Continuous (sourceGaussianIntegrand F a b) := by
  have hK := continuous_Kern 3 ha hab
  unfold sourceGaussianIntegrand
  fun_prop
end Auto
