-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_comp_continuousLinearMap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:51.892694+00:00
-- url     : https://prove2.me/submissions/70963817-f396-41a7-8646-84d40575887e

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
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [ProperSpace F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup K]
    (e : E →L[ℝ] F) {f : F → K} (hf : Continuous f) (x : E) :
    wienerEnvelope (f ∘ e) 1 x ≤ wienerEnvelope f ‖e‖ (e x) := by
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  apply le_csSup
  · exact (isCompact_closedBall (0 : F) ‖e‖).bddAbove_image
      (show Continuous (fun w : F ↦ ‖f (e x + w)‖) by fun_prop).continuousOn
  · refine ⟨e z, ?_, ?_⟩
    · apply Metric.mem_closedBall.mpr
      simpa [dist_eq_norm] using
        (calc
          ‖e z‖ ≤ ‖e‖ * ‖z‖ := e.le_opNorm z
          _ ≤ ‖e‖ * 1 := by
            gcongr
            simpa [Metric.mem_closedBall, dist_eq_norm] using hz
          _ = ‖e‖ := mul_one _)
    · simp only [Function.comp_apply, e.map_add]
end Auto
