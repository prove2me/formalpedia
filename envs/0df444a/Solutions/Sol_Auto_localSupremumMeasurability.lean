-- Prove2me | solution 1 for Auto.localSupremumMeasurability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:30.052927+00:00
-- url     : https://prove2.me/submissions/4d646742-4aa7-460e-b852-2b88e6e7c7ef

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_measurable_wienerEnvelope
public import Theorems.Thm_Auto_upperSemicontinuous_wienerEnvelope

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r : ℝ} (_hr : 0 < r) :
    UpperSemicontinuous (wienerEnvelope f r) ∧ Measurable (wienerEnvelope f r) := by
  exact ⟨upperSemicontinuous_wienerEnvelope hf r, measurable_wienerEnvelope hf r⟩
end Auto
