-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_le_sum_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:02.463234+00:00
-- url     : https://prove2.me/submissions/59acd78f-9f11-426b-b729-ff42edf3d07c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (t : Finset E)
    (hcover : ∀ y ∈ closedBall (0 : E) s, ∃ z ∈ t, y ∈ closedBall z r) (x : E) :
    wienerEnvelope f s x ≤ ∑ z ∈ t, wienerEnvelope f r (x + z) := by
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr hs).image _)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hzt, hyz⟩ := hcover y hy
  calc
    ‖f (x + y)‖ ≤ wienerEnvelope f r (x + z) := by
      unfold wienerEnvelope
      let h : Continuous (fun w : E ↦ ‖f ((x + z) + w)‖) := by fun_prop
      apply le_csSup
      · exact (isCompact_closedBall (0 : E) r).bddAbove_image h.continuousOn
      · refine ⟨y - z, ?_, ?_⟩
        · simpa [Metric.mem_closedBall, dist_eq_norm] using hyz
        · abel_nf
    _ ≤ ∑ z ∈ t, wienerEnvelope f r (x + z) :=
      Finset.single_le_sum (fun w hw ↦ aux_wienerEnvelope_nonneg hf hr _) hzt
end Auto
