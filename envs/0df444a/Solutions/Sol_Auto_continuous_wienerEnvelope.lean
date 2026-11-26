-- Prove2me | solution 1 for Auto.continuous_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:08.990807+00:00
-- url     : https://prove2.me/submissions/376022e1-ce1e-4ff2-8fe4-4534eb1d0b6e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {f : E → F} (hf : Continuous f) (r : ℝ) :
    Continuous (wienerEnvelope f r) := by
  change Continuous (fun x : E ↦
    sSup ((fun z : E ↦ ‖f (x + z)‖) '' closedBall 0 r))
  exact (isCompact_closedBall (0 : E) r).continuous_sSup
    (show Continuous (fun p : E × E ↦ ‖f (p.1 + p.2)‖) by fun_prop)
end Auto
