-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:58.640065+00:00
-- url     : https://prove2.me/theorems/957cbbe4-5c25-4c7f-8836-8ab59eccf48a
-- title:
--   Polynomial Growth Integrals
-- statement:
--   Definitions and structural lemmas for Polynomial Growth Integrals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace subgroupData
def qv (c : Fin 3 → ℂ) (t : ℝ) : ℂ := c 0 + c 1 * t + c 2 * t ^ 2
end subgroupData
end ReciprocityTheory.ChartRestriction.DS.Xi


