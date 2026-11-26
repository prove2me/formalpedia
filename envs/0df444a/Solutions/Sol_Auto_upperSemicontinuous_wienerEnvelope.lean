-- Prove2me | solution 1 for Auto.upperSemicontinuous_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:36.588934+00:00
-- url     : https://prove2.me/submissions/6ce39d02-9ad0-43c8-a35d-a4abee1afed1

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
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (r : ℝ) :
    UpperSemicontinuous (wienerEnvelope f r) :=
  (continuous_wienerEnvelope hf r).upperSemicontinuous
end Auto
