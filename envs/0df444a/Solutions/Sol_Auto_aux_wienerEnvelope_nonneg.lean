-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:34.627777+00:00
-- url     : https://prove2.me/submissions/ca12b666-e97d-4b80-8866-16c5e7777491

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
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) (x : E) :
    0 ≤ wienerEnvelope f r x := by
  unfold wienerEnvelope
  let h : Continuous (fun z : E ↦ ‖f (x + z)‖) := by fun_prop
  calc
    0 ≤ ‖f (x + 0)‖ := norm_nonneg _
    _ ≤ sSup ((fun z : E ↦ ‖f (x + z)‖) '' closedBall 0 r) := by
      apply le_csSup
      · exact (isCompact_closedBall (0 : E) r).bddAbove_image h.continuousOn
      · exact ⟨0, Metric.mem_closedBall_self hr, rfl⟩
end Auto
