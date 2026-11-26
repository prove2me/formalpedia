-- Prove2me | solution 1 for Auto.measurable_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:09.024502+00:00
-- url     : https://prove2.me/submissions/e33bec91-78e0-4f7b-9a92-7be18ccc5d89

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] [MeasurableSpace E] [BorelSpace E] {f : E → F}
    (hf : Continuous f) (r : ℝ) : Measurable (wienerEnvelope f r) :=
  (continuous_wienerEnvelope hf r).measurable
end Auto
