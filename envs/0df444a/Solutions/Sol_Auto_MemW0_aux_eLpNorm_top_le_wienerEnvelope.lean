-- Prove2me | solution 1 for Auto.MemW0.aux_eLpNorm_top_le_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:00.69454+00:00
-- url     : https://prove2.me/submissions/f5bcb257-1e73-4b16-b272-296ac92ccd73

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume
public import Theorems.Thm_Auto_aux_eLpNorm_top_le_of_bound

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) :
    eLpNorm f ∞ volume ≤ ENNReal.ofReal ((∫ x, wienerEnvelope f 1 x) /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  aux_eLpNorm_top_le_of_bound (ae_of_all _ fun x ↦
    aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume hf x)
end MemW0
end Auto
