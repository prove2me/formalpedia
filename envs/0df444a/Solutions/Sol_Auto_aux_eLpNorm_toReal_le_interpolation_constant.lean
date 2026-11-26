-- Prove2me | solution 1 for Auto.aux_eLpNorm_toReal_le_interpolation_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:49.446832+00:00
-- url     : https://prove2.me/submissions/db1fa43f-2785-4883-a726-411fd23208d5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_eLpNorm_toReal_le_of_l1_linf_bounds
public import Theorems.Thm_Auto_aux_rpow_interpolation_constant

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : AEStronglyMeasurable f μ) {q I V : ℝ} (hq : 1 ≤ q)
    (hI : 0 ≤ I) (hV : 0 < V) (hL1 : eLpNorm f 1 μ ≤ ENNReal.ofReal I)
    (hLinf : eLpNorm f ∞ μ ≤ ENNReal.ofReal (I / V)) :
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ≤ V ^ (q⁻¹ - 1) * I := by
  calc
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ≤
        I ^ q⁻¹ * (I / V) ^ (1 - q⁻¹) :=
      aux_eLpNorm_toReal_le_of_l1_linf_bounds hf hq hI (div_nonneg hI hV.le) hL1 hLinf
    _ = V ^ (q⁻¹ - 1) * I := aux_rpow_interpolation_constant hI hV hq
end Auto
