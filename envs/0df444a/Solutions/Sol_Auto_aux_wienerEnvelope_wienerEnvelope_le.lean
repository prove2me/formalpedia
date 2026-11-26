-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_wienerEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:37.857212+00:00
-- url     : https://prove2.me/submissions/e4ac5115-b2d8-417d-bfc2-25bf827783de

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
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (x : E) :
    wienerEnvelope (wienerEnvelope f r) s x ≤ wienerEnvelope f (r + s) x := by
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr hs).image _)
  rintro _ ⟨z, hz, rfl⟩
  change ‖wienerEnvelope f r (x + z)‖ ≤ wienerEnvelope f (r + s) x
  rw [Real.norm_eq_abs, abs_of_nonneg (aux_wienerEnvelope_nonneg hf hr _)]
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr hr).image _)
  rintro _ ⟨w, hw, rfl⟩
  let h : Continuous (fun q : E ↦ ‖f (x + q)‖) := by fun_prop
  apply le_csSup
  · exact (isCompact_closedBall (0 : E) (r + s)).bddAbove_image h.continuousOn
  · refine ⟨z + w, ?_, ?_⟩
    · apply Metric.mem_closedBall.mpr
      calc
        dist (z + w) 0 = ‖z + w‖ := by simp [dist_eq_norm]
        _ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
        _ ≤ s + r := by
          gcongr
          · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
          · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
        _ = r + s := add_comm _ _
    · abel_nf
end Auto
