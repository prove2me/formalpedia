-- Prove2me | solution 1 for Auto.aux_square_endpoint_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:46.75522+00:00
-- url     : https://prove2.me/submissions/f9589018-bfdb-4ebf-8eb9-2ebe8798b5fa

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
theorem _root_.solution {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y * a y - a x * a x‖ₑ ≤
      ∫⁻ z in Set.Icc x y, (2 : ℝ≥0∞) * ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  have hsubset : Set.Icc x y ⊆ Set.Icc α β := by
    intro z hz
    exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hsq := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
    ((ha.mul ha).mono hsubset) hxy
  refine hsq.trans ?_
  apply lintegral_mono_ae
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hzαβ : z ∈ Set.Ioo α β :=
    ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  have hdiff : DifferentiableAt ℝ a z :=
    ((ha z ⟨hzαβ.1.le, hzαβ.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
      (Icc_mem_nhds hzαβ.1 hzαβ.2)
  change ‖deriv (a * a) z‖ₑ ≤ _
  rw [deriv_mul hdiff hdiff]
  rw [show deriv a z * a z + a z * deriv a z = 2 * a z * deriv a z by ring]
  have htwo : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by norm_num [enorm_eq_nnnorm]
  simp [enorm_mul, htwo]
end Auto
