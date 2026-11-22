-- Prove2me | solution 1 for Auto.abs_sub_latticeFloor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:39:37.768278+00:00
-- url     : https://prove2.me/submissions/607c9891-09d3-4e1a-8485-4b55ead53d77

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
theorem _root_.solution {N : ℕ} (hN : 0 < N) (x : Fin d → ℝ) (i : Fin d) :
    |x i - latticeFloor N x i| ≤ (N : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Int.floor_le ((N : ℝ) * x i)
  have h2 := Int.lt_floor_add_one ((N : ℝ) * x i)
  simp only [latticeFloor]
  have key : x i - (⌊(N : ℝ) * x i⌋ : ℝ) / N = ((N : ℝ) * x i - ⌊(N : ℝ) * x i⌋) / N := by
    field_simp
  rw [key, abs_div, abs_of_pos hN', div_le_iff₀ hN', inv_mul_cancel₀ hN'.ne', abs_le]
  constructor <;> linarith
end Auto
