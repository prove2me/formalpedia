-- Prove2me | solution 1 for Auto.abs_gaussianD_le_unif
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:48:06.931042+00:00
-- url     : https://prove2.me/submissions/87a935a5-274f-45e3-ae32-ee935bfaf629

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
namespace Auto
theorem _root_.solution (j : ℕ) {σa σb : ℝ} (ha : 0 < σa) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σa σb, ∀ t, |gaussianD j σ t| ≤ C * Real.exp (-(t ^ 2) / (4 *
      σb)) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j 0
  refine ⟨C * (√σa)⁻¹ ^ (j + 1), by positivity, fun σ hσ t => ?_⟩
  have hσ0 : 0 < σ := ha.trans_le hσ.1
  have h1 := h σ hσ0 t
  simp only [pow_zero, one_mul, mul_one] at h1
  have hs : (√σ)⁻¹ ≤ (√σa)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 ha) (Real.sqrt_le_sqrt hσ.1)
  have he : Real.exp (-(t ^ 2) / (4 * σ)) ≤ Real.exp (-(t ^ 2) / (4 * σb)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith [hσ.2])
  calc |gaussianD j σ t| ≤ C * (√σ)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σ)) := h1
    _ ≤ C * (√σa)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σb)) := by gcongr
end Auto
