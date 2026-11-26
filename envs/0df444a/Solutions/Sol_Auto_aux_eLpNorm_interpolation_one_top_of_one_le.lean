-- Prove2me | solution 1 for Auto.aux_eLpNorm_interpolation_one_top_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:51.131477+00:00
-- url     : https://prove2.me/submissions/e6044f09-3bbe-44d2-be1d-f237697d9dbb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_eLpNorm_interpolation_one_top_of_one_lt

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      (eLpNorm f 1 μ) ^ q⁻¹ * (eLpNorm f ∞ μ) ^ (1 - q⁻¹) := by
  rcases hq.eq_or_lt with rfl | hq
  · norm_num
  exact aux_eLpNorm_interpolation_one_top_of_one_lt hf hq
end Auto
