-- Prove2me | solution 1 for Auto.aux_eLpNorm_le_of_l1_linf_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:54.616334+00:00
-- url     : https://prove2.me/submissions/e685aae7-4cba-490b-8cbb-5345cde1774b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_eLpNorm_interpolation_one_top_of_one_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q)
    {A B : ℝ≥0∞} (hA : eLpNorm f 1 μ ≤ A) (hB : eLpNorm f ∞ μ ≤ B) :
    eLpNorm f (ENNReal.ofReal q) μ ≤ A ^ q⁻¹ * B ^ (1 - q⁻¹) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hqinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hqcomp : 0 ≤ 1 - q⁻¹ := by
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ hq
  calc
    eLpNorm f (ENNReal.ofReal q) μ ≤
        (eLpNorm f 1 μ) ^ q⁻¹ * (eLpNorm f ∞ μ) ^ (1 - q⁻¹) :=
      aux_eLpNorm_interpolation_one_top_of_one_le hf hq
    _ ≤ A ^ q⁻¹ * B ^ (1 - q⁻¹) :=
      mul_le_mul (ENNReal.rpow_le_rpow hA hqinv) (ENNReal.rpow_le_rpow hB hqcomp)
        bot_le bot_le
end Auto
