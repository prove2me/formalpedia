-- Prove2me | solution 1 for Auto.aux_integral_norm_le_integral_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:55.440063+00:00
-- url     : https://prove2.me/submissions/6d7068bf-d0e5-4b91-9ef3-22b65df27838

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_MemW0_aux_integrable_envelope
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope
public import Theorems.Thm_Auto_MemW0_aux_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    (∫ x, ‖f x‖) ≤ ∫ x, wienerEnvelope f 1 x := by
  exact integral_mono hf.aux_integrable.norm hf.aux_integrable_envelope
    (fun x ↦ aux_norm_le_wienerEnvelope hf.aux_continuous zero_le_one x)
end Auto
