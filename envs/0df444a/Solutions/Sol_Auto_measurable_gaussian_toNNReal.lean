-- Prove2me | solution 1 for Auto.measurable_gaussian_toNNReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:36:37.555868+00:00
-- url     : https://prove2.me/submissions/b683cfd4-870c-47e7-b206-cb3c8503cfb9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution (τ : ℝ) : Measurable fun d => (gaussian τ d).toNNReal :=
  (continuous_gaussian' τ).measurable.real_toNNReal
end Auto
