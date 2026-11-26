-- Prove2me | solution 1 for Auto.aux_integrable_slice_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:29.154786+00:00
-- url     : https://prove2.me/submissions/75fc9e35-6ee4-432e-95d8-6b7e3d7ce9b0

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
theorem _root_.solution {m l : ℕ}
    {G : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → ℝ}
    (hG : Continuous G) (hGnonneg : ∀ q, 0 ≤ G q)
    (hK : Integrable (wienerEnvelope G 1)) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun v ↦ G (u, v)) := by
  have hgood_ae :
      ∀ᵐ u' ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
        Integrable (fun v ↦ wienerEnvelope G 1 (u', v)) := by
    exact hK.prod_right_ae
  obtain ⟨u', hu', hu'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball u 1)
    ((measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin m))) u zero_lt_one).ne')
    (ae_restrict_of_ae hgood_ae)
  refine hu'good.mono_nonneg ?_ (ae_of_all _ fun v ↦ hGnonneg (u, v))
    (ae_of_all _ fun v ↦ ?_)
  · fun_prop
  · have hmem : (u, v) ∈ closedBall (u', v) 1 := by
      apply Metric.mem_closedBall.mpr
      simpa only [dist_prod_same_right] using
        (le_of_lt (by simpa [dist_comm] using (Metric.mem_ball.mp hu')))
    simpa [Real.norm_eq_abs, abs_of_nonneg (hGnonneg (u, v))] using
      (aux_norm_le_wienerEnvelope_of_mem_closedBall hG hmem)
end Auto
