-- Prove2me | solution 1 for Auto.integrable_wienerEnvelope_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:27.74936+00:00
-- url     : https://prove2.me/submissions/f09507de-7e4b-4a08-9f38-0af2e01d5079

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : Continuous f) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    Integrable (wienerEnvelope f r) ↔ Integrable (wienerEnvelope f s) := by
  constructor
  · exact aux_integrable_wienerEnvelope_of_integrable hf hr (le_of_lt hs)
  · exact aux_integrable_wienerEnvelope_of_integrable hf hs (le_of_lt hr)
end Auto
