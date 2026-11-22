-- Prove2me | solution 1 for Auto.abs_gaussianD_le_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:25:59.912885+00:00
-- url     : https://prove2.me/submissions/fb9b9c46-52c1-44d5-bb62-3878a20e7b74

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
open Real
namespace Auto
theorem _root_.solution (j : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ M : ℝ, ∀ t, |gaussianD j σ t| ≤ M := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j 0
  refine ⟨C * (√σ) ^ 0 * (√σ)⁻¹ ^ (j + 1), fun t => ?_⟩
  have := h σ hσ t
  rw [pow_zero, one_mul] at this
  refine this.trans ?_
  have : Real.exp (-(t ^ 2) / (4 * σ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ t ^ 2 / (4 * σ) := by positivity
    rw [neg_div]; linarith
  have : 0 ≤ C * (√σ) ^ 0 * (√σ)⁻¹ ^ (j + 1) := by positivity
  nlinarith [Real.exp_pos (-(t ^ 2) / (4 * σ))]
end Auto
