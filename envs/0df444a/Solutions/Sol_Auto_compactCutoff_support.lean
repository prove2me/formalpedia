-- Prove2me | solution 1 for Auto.compactCutoff_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:41:14.992791+00:00
-- url     : https://prove2.me/submissions/77cb4a20-a961-4925-b390-00b84be06684

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
theorem _root_.solution (n : ℕ) : HasCompactSupport (compactCutoff n) := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 (n + 1 : ℝ)) ?_
  intro p hp
  have h : (n : ℝ) + 1 < ‖p‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  simp [compactCutoff, min_eq_right (by linarith : (n : ℝ) + 1 - ‖p‖ ≤ 1),
    max_eq_left (by linarith : (n : ℝ) + 1 - ‖p‖ ≤ 0)]
end Auto
