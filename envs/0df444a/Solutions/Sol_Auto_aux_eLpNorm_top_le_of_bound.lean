-- Prove2me | solution 1 for Auto.aux_eLpNorm_top_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:31.531808+00:00
-- url     : https://prove2.me/submissions/c9c48677-4978-4d59-bfb5-cb8b3373870d

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
    {f : E → 𝕜} {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    eLpNorm f ∞ μ ≤ ENNReal.ofReal B := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hB
end Auto
