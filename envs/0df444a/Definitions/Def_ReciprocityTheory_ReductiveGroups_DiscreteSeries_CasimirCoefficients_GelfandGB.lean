-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:17.853084+00:00
-- url     : https://prove2.me/theorems/7669cabd-9d3e-4d89-9d29-3187a2952e63
-- title:
--   Gelfand GB
-- statement:
--   Definitions and structural lemmas for Gelfand GB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandGB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H] [FiniteDimensional ℂ H]
  {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
  (ν : Measure K) [IsFiniteMeasure ν]
  (c : K → H →L[ℂ] H) (hc : Continuous c) {U Ω : Set H} (hU : IsOpen U) (hΩ : IsOpen Ω)
  (hUΩ : ∀ x ∈ U, ∀ k, c k x ∈ Ω)
def Mop {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : K → E' →L[ℂ] E) (k : K) : (H →L[ℂ] E') →L[ℂ] (H →L[ℂ] E) :=
  (ContinuousLinearMap.compL ℂ H E' E (L k)).comp ((ContinuousLinearMap.compL ℂ H H E').flip (c k))
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB


