-- Prove2me | solution 1 for Auto.aux_integrable_of_memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:20.076172+00:00
-- url     : https://prove2.me/submissions/6a6350e1-2d40-498c-a190-06ca78cff97f

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg


set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
namespace Auto
theorem _root_.solution {E 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup 𝕜]
    {f : E → 𝕜} (hf : MemW0 f) : Integrable f := by
  refine hf.2.mono hf.1.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (aux_wienerEnvelope_nonneg hf.1 zero_le_one x)] using
      aux_norm_le_wienerEnvelope hf.1 zero_le_one x
end Auto
