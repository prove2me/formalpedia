-- Prove2me | solution 1 for Auto.aux_continuous_integral_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:48:41.067867+00:00
-- url     : https://prove2.me/submissions/b3f1c950-c74f-4b53-b5a9-88e1ac744b7c

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
theorem _root_.solution {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    Continuous (fun u ↦ ∫ v, f (u, v)) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  have hgood_ae :
      ∀ᵐ u' ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
        Integrable (fun v ↦ wienerEnvelope f 1 (u', v)) := by
    exact hf.2.prod_right_ae
  obtain ⟨u', hu', hu'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball u₀ (1 / 2))
    ((measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin m))) u₀ (by norm_num)).ne')
    (ae_restrict_of_ae hgood_ae)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v ↦ wienerEnvelope f 1 (u', v))
  · filter_upwards [] with u
    exact (hf.1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds u₀ (by norm_num : 0 < (1 / 2 : ℝ))] with u hu
    filter_upwards [] with v
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
    apply Metric.mem_closedBall.mpr
    rw [Prod.dist_eq]
    apply max_le
    · change dist u u' ≤ 1
      apply le_of_lt
      calc
        dist u u' ≤ dist u u₀ + dist u₀ u' := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (Metric.mem_ball.mp hu)
          (by simpa [dist_comm] using (Metric.mem_ball.mp hu'))
        _ = 1 := by norm_num
    · change dist v v ≤ 1
      simp
  · exact hu'good
  · filter_upwards [] with v
    exact hf.1.continuousAt.tendsto.comp
      (continuous_id.prodMk continuous_const).continuousAt
end Auto
