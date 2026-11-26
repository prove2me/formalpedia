-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_eq_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:23.44469+00:00
-- url     : https://prove2.me/submissions/1e9e48b9-b131-4763-b983-06c105895014

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
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : E → F} {r : ℝ} {x : E} :
    wienerEnvelope f r x = sSup ((fun y : E ↦ ‖f y‖) '' closedBall x r) := by
  unfold wienerEnvelope
  congr 1
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨x + z, ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - x, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    · simp
end Auto
