-- Prove2me | solution 1 for Auto.sqrt_hsSq_le_of_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:24:26.050892+00:00
-- url     : https://prove2.me/submissions/e3d47329-5202-4096-8730-529af8e29839

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hsSq_le_of_entry_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]
namespace Auto
theorem _root_.solution (K : Matrix κ κ ℂ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ a b, ‖K a b‖ ≤ c) :
    √(hsSq K) ≤ Fintype.card κ * c := by
  rw [Real.sqrt_le_left (by positivity)]
  have := hsSq_le_of_entry_le K h
  nlinarith
end Auto
