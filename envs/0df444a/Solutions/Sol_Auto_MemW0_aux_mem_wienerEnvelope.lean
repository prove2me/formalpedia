-- Prove2me | solution 1 for Auto.MemW0.aux_mem_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:44.100771+00:00
-- url     : https://prove2.me/submissions/8a9167ea-1cb4-4630-b8a0-88a9b0733c86

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_wienerEnvelope_le
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddRightInvariant (volume : Measure E)]
    [NormedAddCommGroup F] {f : E → F} (hf : MemW0 f) {r : ℝ} (hr : 0 ≤ r) :
    MemW0 (wienerEnvelope f r) := by
  have hcont : Continuous (wienerEnvelope f r) := continuous_wienerEnvelope hf.1 r
  refine ⟨hcont, ?_⟩
  have hinter : Integrable (wienerEnvelope f (r + 1)) :=
    aux_integrable_wienerEnvelope_of_integrable' hf.1 zero_lt_one (by linarith) hf.2
  refine hinter.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_wienerEnvelope_le hf.1 hr zero_le_one x
end MemW0
end Auto
