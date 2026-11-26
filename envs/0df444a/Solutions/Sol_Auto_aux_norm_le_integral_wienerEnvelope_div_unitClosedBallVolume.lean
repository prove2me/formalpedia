-- Prove2me | solution 1 for Auto.aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:11.544522+00:00
-- url     : https://prove2.me/submissions/82bfe628-4eb2-4857-8468-f2e32e62860a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope
public import Theorems.Thm_Auto_aux_unitClosedBallVolume_pos

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖f x‖ ≤ (∫ y, wienerEnvelope f 1 y) /
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  rw [le_div_iff₀ (aux_unitClosedBallVolume_pos (d := d))]
  exact aux_norm_mul_unitClosedBallVolume_le_integral_wienerEnvelope hf x
end Auto
