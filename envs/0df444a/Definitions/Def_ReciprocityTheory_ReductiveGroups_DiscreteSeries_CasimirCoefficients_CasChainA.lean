-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:03.269057+00:00
-- url     : https://prove2.me/theorems/d5331dc1-1bfd-418e-aafa-4327995ecc78
-- title:
--   Cas Chain A
-- statement:
--   Definitions and structural lemmas for Cas Chain A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasChainA.lean

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
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
namespace ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def ccaKappa (ρ : ℝ) (θ : ℝ) : ℂ := deriv (circleMap 0 ρ) θ * (1 / (circleMap 0 ρ θ - 0) ^ 2)
end ReciprocityTheory.ChartRestriction.DS.S7


