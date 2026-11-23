-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_BesselVectors_ClmInt
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_BesselVectors_ClmInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:47.417555+00:00
-- url     : https://prove2.me/theorems/044e1016-cc98-4502-aa90-13427e9ddaad
-- title:
--   Clm Int
-- statement:
--   Definitions and structural lemmas for Clm Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/BesselVectors/ClmInt.lean

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
open MeasureTheory
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.TopClm
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
end ReciprocityTheory.ChartRestriction.DS.Lap.TopClm


