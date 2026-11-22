-- Prove2me | solution 1 for Auto.exists_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:54:47.353562+00:00
-- url     : https://prove2.me/submissions/8d7f6cf4-9a0c-42dd-a1e6-fc6fd6140cbb

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
theorem _root_.solution {f : ℝ × ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ ρ, 0 ≤ ρ ∧ ∀ p, ρ < ‖p‖ → f p = 0 := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 0, le_max_right _ _, fun p hp => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hr h
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left r 0]
end Auto
