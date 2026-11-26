-- Prove2me | solution 1 for Auto.MemW0.aux_comp_continuousLinearMap_of_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:20.562902+00:00
-- url     : https://prove2.me/submissions/c6c578f8-4d0a-4bcd-a06b-c6bcbd4783f7

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_comp_continuousLinearMap_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution
    {E F K : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [ProperSpace E] [ProperSpace F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]
    [NormedAddCommGroup K] {f : F → K} (hf : MemW0 f) (e : E →L[ℝ] F)
    (he : MeasurePreserving e volume volume)
    (hr : Integrable (wienerEnvelope f ‖e‖)) :
    MemW0 (f ∘ e) := by
  refine ⟨hf.1.comp e.continuous, ?_⟩
  have hcomp : Integrable (wienerEnvelope f ‖e‖ ∘ e) :=
    he.integrable_comp_of_integrable hr
  refine hcomp.mono_nonneg
    (continuous_wienerEnvelope (hf.1.comp e.continuous) 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg (hf.1.comp e.continuous) zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_comp_continuousLinearMap_le e hf.1 x
end MemW0
end Auto
