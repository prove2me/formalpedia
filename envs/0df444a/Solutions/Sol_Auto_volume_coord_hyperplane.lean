-- Prove2me | solution 1 for Auto.volume_coord_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:03:40.742883+00:00
-- url     : https://prove2.me/submissions/bbe28459-d856-422e-b520-cb3ea39ad1ee

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Auto
theorem _root_.solution (i : Fin d) (a : ℝ) : volume {x : Fin d → ℝ | x i = a} = 0 := by
  have : {x : Fin d → ℝ | x i = a} = (Function.eval i : (Fin d → ℝ) → ℝ) ⁻¹' ({a} : Set ℝ) := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ (Real.volume_singleton)
end Auto
