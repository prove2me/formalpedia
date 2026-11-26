-- Prove2me | solution 1 for Auto.aux_unitClosedBallVolume_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:07.402132+00:00
-- url     : https://prove2.me/submissions/05516a24-452e-402a-8971-97c1028c5649

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
theorem _root_.solution {d : ℕ} :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 zero_lt_one).ne'
    measure_closedBall_lt_top.ne
end Auto
