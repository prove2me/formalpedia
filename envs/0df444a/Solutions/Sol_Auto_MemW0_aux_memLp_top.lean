-- Prove2me | solution 1 for Auto.MemW0.aux_memLp_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:51.652556+00:00
-- url     : https://prove2.me/submissions/8d6f3ba5-28da-45c7-b198-0a1c1b467bb6

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : MemLp f ∞ volume := by
  apply memLp_top_of_bound hf.aux_continuous.aestronglyMeasurable
    ((∫ y, wienerEnvelope f 1 y) /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1))
  exact ae_of_all _ fun x ↦ aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume hf x
end MemW0
end Auto
