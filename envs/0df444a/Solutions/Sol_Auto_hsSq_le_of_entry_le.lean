-- Prove2me | solution 1 for Auto.hsSq_le_of_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:42.06959+00:00
-- url     : https://prove2.me/submissions/27d0e168-5a25-487c-b23a-777a5efac335

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
open Auto
noncomputable section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]
namespace Auto
theorem _root_.solution (K : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖K a b‖ ≤ c) :
    hsSq K ≤ (Fintype.card κ : ℝ) ^ 2 * c ^ 2 := by
  unfold hsSq
  calc ∑ a, ∑ b, ‖K a b‖ ^ 2 ≤ ∑ _a : κ, ∑ _b : κ, c ^ 2 := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (h a b) 2
    _ = _ := by simp; ring
end Auto
