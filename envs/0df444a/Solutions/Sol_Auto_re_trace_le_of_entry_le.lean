-- Prove2me | solution 1 for Auto.re_trace_le_of_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:52.815927+00:00
-- url     : https://prove2.me/submissions/9f7f8e64-36cb-410f-bee7-3977bcb01319

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
theorem _root_.solution (Γ : Matrix κ κ ℂ) {c : ℝ} (h : ∀ a b, ‖Γ a b‖ ≤ c) :
    Γ.trace.re ≤ Fintype.card κ * c := by
  rw [Matrix.trace, Complex.re_sum]
  calc ∑ a, (Γ a a).re ≤ ∑ _a : κ, c :=
        Finset.sum_le_sum fun a _ => (Complex.re_le_norm _).trans (h a a)
    _ = _ := by simp
end Auto
