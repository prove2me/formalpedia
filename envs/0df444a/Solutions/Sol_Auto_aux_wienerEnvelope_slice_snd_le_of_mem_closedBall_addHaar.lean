-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:46.287093+00:00
-- url     : https://prove2.me/submissions/073894aa-5b23-42d1-9da3-f4f23447108e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [NormedAddCommGroup K] {f : E × F → K} (hf : Continuous f)
    {v v' : F} (hv' : v' ∈ closedBall v 1) (u : E) :
    wienerEnvelope (fun u => f (u, v)) 1 u ≤ wienerEnvelope f 1 (u, v') := by
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf
  apply Metric.mem_closedBall.mpr
  rw [Prod.dist_eq]
  apply max_le
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  · simpa [dist_comm] using Metric.mem_closedBall.mp hv'
end Auto
