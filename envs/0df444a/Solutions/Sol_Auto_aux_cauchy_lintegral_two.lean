-- Prove2me | solution 1 for Auto.aux_cauchy_lintegral_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:49.519967+00:00
-- url     : https://prove2.me/submissions/4ce290f7-be06-473c-ae70-ce5c49fd6b14

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {mu : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f mu) :
    ∫⁻ t, f t ∂mu ≤ (∫⁻ t, f t ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
      (mu Set.univ) ^ ((2 : ℝ)⁻¹) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  simpa [one_div] using
    (ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq hf (g := fun _ : ℝ ↦ 1)
      measurable_const.aemeasurable)
end Auto
