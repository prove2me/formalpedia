-- Prove2me | solution 1 for Auto.memW0_iff_integrable_wienerEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:49.654412+00:00
-- url     : https://prove2.me/submissions/62284cd3-6151-410b-a96b-cd7a846972e7

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_integrable_wienerEnvelope_iff

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    MemW0 f ↔ Integrable (wienerEnvelope f r) := by
  simp only [MemW0]
  constructor
  · rintro ⟨-, h⟩
    exact (integrable_wienerEnvelope_iff hf zero_lt_one hr).mp h
  · intro h
    exact ⟨hf, (integrable_wienerEnvelope_iff hf hr zero_lt_one).mp h⟩
end Auto
