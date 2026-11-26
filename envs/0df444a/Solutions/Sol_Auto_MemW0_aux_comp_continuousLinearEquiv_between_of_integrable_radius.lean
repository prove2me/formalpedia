-- Prove2me | solution 1 for Auto.MemW0.aux_comp_continuousLinearEquiv_between_of_integrable_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:47:16.501671+00:00
-- url     : https://prove2.me/submissions/6f30ae43-18da-4f46-88fe-da7fcd9adc9b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_comp_continuousLinearMap_le
public import Theorems.Thm_Auto_aux_integrable_comp_continuousLinearEquiv_between

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
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {f : F → K} (hf : MemW0 f) (e : E ≃L[ℝ] F)
    (hr : Integrable (wienerEnvelope f ‖(e : E →L[ℝ] F)‖)) :
    MemW0 (f ∘ e) := by
  refine ⟨hf.1.comp e.continuous, ?_⟩
  have hcomp : Integrable (wienerEnvelope f ‖(e : E →L[ℝ] F)‖ ∘ e) :=
    aux_integrable_comp_continuousLinearEquiv_between hr e
  refine hcomp.mono_nonneg
    (continuous_wienerEnvelope (hf.1.comp e.continuous) 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg (hf.1.comp e.continuous) zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_comp_continuousLinearMap_le (e : E →L[ℝ] F) hf.1 x
end MemW0
end Auto
