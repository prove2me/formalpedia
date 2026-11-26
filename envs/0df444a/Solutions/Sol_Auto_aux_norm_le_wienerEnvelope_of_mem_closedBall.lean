-- Prove2me | solution 1 for Auto.aux_norm_le_wienerEnvelope_of_mem_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:11.069067+00:00
-- url     : https://prove2.me/submissions/d90287c9-43a1-4349-bac5-845ba12d24b2

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
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E]
    [ProperSpace E] [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r : ℝ}
    {x y : E} (hy : y ∈ closedBall x r) :
    ‖f y‖ ≤ wienerEnvelope f r x := by
  unfold wienerEnvelope
  let h : Continuous (fun z : E ↦ ‖f (x + z)‖) := by fun_prop
  apply le_csSup
  · exact (isCompact_closedBall (0 : E) r).bddAbove_image h.continuousOn
  · refine ⟨y - x, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    · abel_nf
end Auto
