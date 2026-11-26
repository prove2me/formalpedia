-- Prove2me | solution 1 for Auto.MemW0.aux_memW0_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:25.036089+00:00
-- url     : https://prove2.me/submissions/d141b8d5-2c38-4f85-8382-01264dceaeb3

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    MemW0 (fun v ↦ f (u, v)) := by
  have hgood_ae :
      ∀ᵐ u' ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
        Integrable (fun v ↦ wienerEnvelope f 1 (u', v)) := by
    exact hf.2.prod_right_ae
  obtain ⟨u', hu', hu'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball u 1)
    ((measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin m))) u zero_lt_one).ne')
    (ae_restrict_of_ae hgood_ae)
  have hslice : Continuous (fun v ↦ f (u, v)) :=
    hf.1.comp (continuous_const.prodMk continuous_id)
  refine ⟨hslice, hu'good.mono_nonneg
    (continuous_wienerEnvelope hslice 1).aestronglyMeasurable
    (ae_of_all _ fun v ↦ aux_wienerEnvelope_nonneg hslice zero_le_one v)
    (ae_of_all _ fun v ↦ ?_)⟩
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
  apply Metric.mem_closedBall.mpr
  rw [Prod.dist_eq]
  apply max_le
  · exact le_of_lt (by simpa [dist_comm] using (Metric.mem_ball.mp hu'))
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
end MemW0
end Auto
