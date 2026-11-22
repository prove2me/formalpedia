-- Prove2me | solution 1 for Auto.abs_Gm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:50:23.341918+00:00
-- url     : https://prove2.me/submissions/d0f5999b-400a-430f-a30a-0b4814fe811f

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_gaussianD_le_unif

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
namespace Auto
theorem _root_.solution (m : ℕ) {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc sa sb, ∀ p, |Gm β m s p| ≤ C * Real.exp (-(p 0 + p 1 + p 2) ^
      2 / (4 * (β * sb))) := by
  obtain ⟨C, hC, h⟩ := abs_gaussianD_le_unif m (σa := β * sa) (σb := β * sb) (by positivity)
  refine ⟨C, hC, fun s hs p => ?_⟩
  have := h (β * s) ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩ (p 0 + p 1 + p 2)
  simpa [Gm, neg_div] using this
end Auto
