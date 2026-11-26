-- Prove2me | solution 1 for Auto.aux_norm_le_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:37.684309+00:00
-- url     : https://prove2.me/submissions/f2098610-7063-4bfe-9db4-123711d5a46b

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
    ‖f x‖ ≤ wienerEnvelope f r x := by
  unfold wienerEnvelope
  let h : Continuous (fun z : E ↦ ‖f (x + z)‖) := by fun_prop
  simpa using
    (le_csSup ((isCompact_closedBall (0 : E) r).bddAbove_image h.continuousOn)
      ⟨0, Metric.mem_closedBall_self hr, rfl⟩)
end Auto
