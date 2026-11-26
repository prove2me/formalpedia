-- Prove2me | solution 1 for Auto.MemW0.aux_memW0_slice_snd_of_addHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:10.014863+00:00
-- url     : https://prove2.me/submissions/e0e1d9c4-ab49-4d22-a5ad-a9406245c8de

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
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)]
    [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : E × F → K} (hf : MemW0 f) (v : F) :
    MemW0 (fun u ↦ f (u, v)) := by
  have hgood_ae :
      ∀ᵐ v' ∂(volume : Measure F),
        Integrable (fun u ↦ wienerEnvelope f 1 (u, v')) := by
    exact hf.2.prod_left_ae
  obtain ⟨v', hv', hv'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball v 1) ((measure_ball_pos (volume : Measure F) v zero_lt_one).ne')
    (ae_restrict_of_ae hgood_ae)
  have hslice : Continuous (fun u ↦ f (u, v)) :=
    hf.1.comp (continuous_id.prodMk continuous_const)
  refine ⟨hslice, hv'good.mono_nonneg
    (continuous_wienerEnvelope hslice 1).aestronglyMeasurable
    (ae_of_all _ fun u ↦ aux_wienerEnvelope_nonneg hslice zero_le_one u)
    (ae_of_all _ fun u ↦ ?_)⟩
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
  apply Metric.mem_closedBall.mpr
  rw [Prod.dist_eq]
  apply max_le
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  · exact le_of_lt (by simpa [dist_comm] using (Metric.mem_ball.mp hv'))
end MemW0
end Auto
