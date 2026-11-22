-- Prove2me | solution 1 for Auto.compactCutoff_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:20.222145+00:00
-- url     : https://prove2.me/submissions/da5cd30e-7c78-49f1-80e2-4bac094b6cb2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
theorem _root_.solution (p : ℝ × ℝ) :
    Tendsto (fun n => compactCutoff n p) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖p‖)]
    with n hn
  simp [compactCutoff, min_eq_left (by linarith : (1 : ℝ) ≤ n + 1 - ‖p‖)]
end Auto
