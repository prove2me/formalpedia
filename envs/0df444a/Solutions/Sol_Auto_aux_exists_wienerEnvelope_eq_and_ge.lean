-- Prove2me | solution 1 for Auto.aux_exists_wienerEnvelope_eq_and_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:27.133561+00:00
-- url     : https://prove2.me/submissions/a20047f8-db1a-4dbe-b7d5-b5375f755be0

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
    ∃ z ∈ closedBall (0 : E) r, wienerEnvelope f r x = ‖f (x + z)‖ ∧
      ∀ w ∈ closedBall (0 : E) r, ‖f (x + w)‖ ≤ ‖f (x + z)‖ := by
  let h : Continuous (fun z : E ↦ ‖f (x + z)‖) := by fun_prop
  obtain ⟨z, hz, hEq, hzmax⟩ :=
    (isCompact_closedBall (0 : E) r).exists_sSup_image_eq_and_ge
      (Metric.nonempty_closedBall.mpr hr) h.continuousOn
  exact ⟨z, hz, hEq, hzmax⟩
end Auto
