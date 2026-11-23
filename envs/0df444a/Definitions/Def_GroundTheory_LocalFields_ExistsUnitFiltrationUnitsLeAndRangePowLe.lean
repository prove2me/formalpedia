-- Prove2me | Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
-- name    : GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.504391+00:00
-- url     : https://prove2.me/theorems/58df0aa9-e84e-4a7a-99c9-2a688453a02a
-- title:
--   Exists Unit Filtration Units Le And Range Pow Le
-- statement:
--   Definitions and structural lemmas for Exists Unit Filtration Units Le And Range Pow Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
noncomputable def unitFiltrationUnits (n : ℕ) : Subgroup Kˣ :=
  (unitFiltration K n).map (unitsIncl K)
variable {K}
end GroundTheory.LocalField


