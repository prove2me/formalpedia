-- Prove2me | solution 1 for Auto.aux_eLpNorm_toReal_le_of_l1_linf_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:54.748291+00:00
-- url     : https://prove2.me/submissions/25ce9c2b-bf00-4d29-beaa-933f126236a7

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_eLpNorm_le_of_l1_linf_bounds

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
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : eLpNorm f 1 μ ≤ ENNReal.ofReal A)
    (hB : eLpNorm f ∞ μ ≤ ENNReal.ofReal B) :
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ≤ A ^ q⁻¹ * B ^ (1 - q⁻¹) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hqinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hqcomp : 0 ≤ 1 - q⁻¹ := by
    rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ hq
  have hbound := aux_eLpNorm_le_of_l1_linf_bounds hf hq hA hB
  have htop : (ENNReal.ofReal A) ^ q⁻¹ * (ENNReal.ofReal B) ^ (1 - q⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hqinv ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hqcomp ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono htop hbound
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hA0, ENNReal.toReal_ofReal hB0] using hreal
end Auto
