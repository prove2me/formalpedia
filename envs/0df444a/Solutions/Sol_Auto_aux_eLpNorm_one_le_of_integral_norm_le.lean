-- Prove2me | solution 1 for Auto.aux_eLpNorm_one_le_of_integral_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:17.158332+00:00
-- url     : https://prove2.me/submissions/1542a375-c35e-4b88-8869-bdf258f3f4f5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup 𝕜] {μ : Measure E}
    {f : E → 𝕜} (hf : Integrable f μ) {I : ℝ} (hI : (∫ x, ‖f x‖ ∂μ) ≤ I) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal I := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have htop : (∫⁻ x, ‖f x‖ₑ ∂μ) ≠ ∞ := by
    simpa only [eLpNorm_one_eq_lintegral_enorm] using
      (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal htop, ← integral_norm_eq_lintegral_enorm hf.1]
  exact ENNReal.ofReal_le_ofReal hI
end Auto
