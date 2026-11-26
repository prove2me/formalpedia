-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_mono_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:41.643144+00:00
-- url     : https://prove2.me/submissions/dc56d30a-3917-4716-8a2b-640cc03b3867

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
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 ≤ r)
    (hrs : r ≤ s) (x : E) :
    wienerEnvelope f r x ≤ wienerEnvelope f s x := by
  unfold wienerEnvelope
  apply csSup_le_csSup
  · let h : Continuous (fun z : E ↦ ‖f (x + z)‖) := by fun_prop
    exact (isCompact_closedBall (0 : E) s).bddAbove_image h.continuousOn
  · exact (Metric.nonempty_closedBall.mpr hr).image _
  · exact Set.image_mono (closedBall_subset_closedBall hrs)
end Auto
