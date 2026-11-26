-- Prove2me | solution 1 for Auto.aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:04.489736+00:00
-- url     : https://prove2.me/submissions/e5374c16-4014-41c9-b212-2bb3cccf3790

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_quantitative_slice_average_addHaar_snd
public import Theorems.Thm_Auto_aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : E × F → K} (hf : MemW0 f) (v : F) :
    (∫ u, wienerEnvelope (fun u => f (u, v)) 1 u) ≤
      ((volume : Measure F).real (closedBall 0 1))⁻¹ * ∫ p, wienerEnvelope f 1 p := by
  let G : E × F → ℝ := wienerEnvelope f 1
  let H : E → ℝ := wienerEnvelope (fun u => f (u, v)) 1
  have hfin : Integrable G (volume.prod volume) := by
    change Integrable (wienerEnvelope f 1) (volume.prod volume)
    rw [← Measure.volume_eq_prod E F]
    exact hf.2
  have hmain : (volume : Measure F).real (closedBall 0 1) * ∫ u, H u ≤
      ∫ p, G p ∂(volume.prod volume) := by
    apply aux_quantitative_slice_average_addHaar_snd hfin
      (fun p => aux_wienerEnvelope_nonneg hf.1 zero_le_one p)
      (continuous_wienerEnvelope (hf.1.comp (continuous_id.prodMk continuous_const)) 1)
      (fun u => aux_wienerEnvelope_nonneg
        (hf.1.comp (continuous_id.prodMk continuous_const)) zero_le_one u)
      v
    intro v' hv' u
    exact aux_wienerEnvelope_slice_snd_le_of_mem_closedBall_addHaar hf.1 hv' u
  have hVpos : 0 < (volume : Measure F).real (closedBall (0 : F) 1) := by
    apply ENNReal.toReal_pos
    · exact (measure_ball_pos (volume : Measure F) 0 zero_lt_one).trans_le
        (measure_mono ball_subset_closedBall) |>.ne'
    · exact measure_closedBall_lt_top.ne
  let V : ℝ := (volume : Measure F).real (closedBall 0 1)
  have hVne : V ≠ 0 := ne_of_gt (by simpa only [V] using hVpos)
  have hmain' : V * ∫ u, H u ≤ ∫ p, G p := by
    simpa only [V, Measure.volume_eq_prod] using hmain
  change (∫ u, H u) ≤ V⁻¹ * ∫ p, G p
  calc
    (∫ u, H u) = V⁻¹ * (V * ∫ u, H u) := by
      field_simp [hVne]
    _ ≤ V⁻¹ * ∫ p, G p :=
      mul_le_mul_of_nonneg_left hmain' (inv_nonneg.mpr (le_of_lt hVpos))
end Auto
