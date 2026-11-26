-- Prove2me | solution 1 for Auto.MemW0.eLpNorm_toReal_le_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:38.773222+00:00
-- url     : https://prove2.me/submissions/0b0d5040-2953-4279-a2f0-a1e808b04919

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_unitClosedBallVolume_pos
public import Theorems.Thm_Auto_aux_eLpNorm_toReal_le_interpolation_constant
public import Theorems.Thm_Auto_MemW0_aux_eLpNorm_one_le_wienerEnvelope
public import Theorems.Thm_Auto_MemW0_aux_eLpNorm_top_le_wienerEnvelope

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    {q : ℝ} (hq : 1 ≤ q) :
    (eLpNorm f (ENNReal.ofReal q) volume).toReal ≤
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ^ (q⁻¹ - 1) *
        ∫ x, wienerEnvelope f 1 x := by
  apply aux_eLpNorm_toReal_le_interpolation_constant hf.aux_continuous.aestronglyMeasurable hq
  · exact integral_nonneg fun x ↦ aux_wienerEnvelope_nonneg hf.aux_continuous zero_le_one x
  · exact aux_unitClosedBallVolume_pos
  · exact hf.aux_eLpNorm_one_le_wienerEnvelope
  · exact hf.aux_eLpNorm_top_le_wienerEnvelope
end MemW0
end Auto
