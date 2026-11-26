-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_fintype_tensor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:19.247832+00:00
-- url     : https://prove2.me/submissions/a6320b0d-25b7-421d-a31d-15167440d798

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
theorem _root_.solution {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, Continuous (f i))
    (x : ∀ i, EuclideanSpace ℝ (Fin (d i))) :
    wienerEnvelope (fun y : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (y i)) 1 x ≤
      ∏ i, wienerEnvelope (f i) 1 (x i) := by
  classical
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  change ‖∏ i, f i ((x + z) i)‖ ≤ ∏ i, wienerEnvelope (f i) 1 (x i)
  rw [norm_prod]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _
    exact norm_nonneg _
  · intro i _
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall (hf i)
    have hz_norm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzi : ‖z i‖ ≤ 1 := (norm_le_pi_norm z i).trans hz_norm
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzi
end Auto
