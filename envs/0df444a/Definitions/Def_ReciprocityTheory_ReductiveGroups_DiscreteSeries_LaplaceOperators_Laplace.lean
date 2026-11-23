-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_Laplace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:39.092365+00:00
-- url     : https://prove2.me/theorems/a2219b7b-50a5-4dc6-b597-714eacfc2533
-- title:
--   Laplace
-- statement:
--   Definitions and structural lemmas for Laplace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/Laplace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology Matrix
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace


