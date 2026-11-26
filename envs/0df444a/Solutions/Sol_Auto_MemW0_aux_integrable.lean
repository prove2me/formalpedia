-- Prove2me | solution 1 for Auto.MemW0.aux_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:49.406662+00:00
-- url     : https://prove2.me/submissions/3f4c38b0-b23e-4ab6-8e4c-1c0fb68f619e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_MemW0_aux_integrable_envelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : Integrable f := by
  refine hf.aux_integrable_envelope.mono hf.aux_continuous.aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (aux_wienerEnvelope_nonneg hf.aux_continuous zero_le_one x)]
    using aux_norm_le_wienerEnvelope hf.aux_continuous zero_le_one x
end MemW0
end Auto
