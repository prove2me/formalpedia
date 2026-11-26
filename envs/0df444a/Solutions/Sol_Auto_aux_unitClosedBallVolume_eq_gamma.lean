-- Prove2me | solution 1 for Auto.aux_unitClosedBallVolume_eq_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:02.345663+00:00
-- url     : https://prove2.me/submissions/42070382-4c06-42bf-a642-d0a50985a17e

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
theorem _root_.solution {d : ℕ} (hd : 0 < d) :
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) =
      (Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  change (volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal = _
  rw [EuclideanSpace.volume_closedBall]
  simp only [ENNReal.ofReal_one, Fintype.card_fin, one_pow, one_mul,
    ENNReal.toReal_ofReal_eq_iff]
  positivity
end Auto
