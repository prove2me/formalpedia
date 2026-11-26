-- Prove2me | solution 1 for Auto.MemW0.aux_integrable_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:38.9398+00:00
-- url     : https://prove2.me/submissions/1a94f447-feec-4d2f-9b6a-ea76fc7b8f48

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
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
theorem _root_.solution {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) : Integrable f := by
  refine hf.2.mono hf.1.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (aux_wienerEnvelope_nonneg hf.1 zero_le_one x)]
    using aux_norm_le_wienerEnvelope hf.1 zero_le_one x
end MemW0
end Auto
