-- Prove2me | solution 1 for Auto.aux_continuous_integral_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:40.374861+00:00
-- url     : https://prove2.me/submissions/d920956f-a95d-4723-8afb-aada80ee48c4

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
namespace Auto
theorem _root_.solution {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    Continuous (fun u ↦ ∫ p, f (u, p)) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  have hgood_ae :
      ∀ᵐ u' ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Integrable (fun p ↦ wienerEnvelope f 1 (u', p)) := by
    exact hf.2.prod_right_ae
  obtain ⟨u', hu', hu'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball u₀ (1 / 2))
    ((measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) u₀ (by norm_num)).ne')
    (ae_restrict_of_ae hgood_ae)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p ↦ wienerEnvelope f 1 (u', p))
  · filter_upwards [] with u
    exact (hf.1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds u₀ (by norm_num : 0 < (1 / 2 : ℝ))] with u hu
    filter_upwards [] with p
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
    · change dist p p ≤ 1
      simp
  · exact hu'good
  · filter_upwards [] with p
    exact hf.1.continuousAt.tendsto.comp
      (continuous_id.prodMk continuous_const).continuousAt
end Auto
