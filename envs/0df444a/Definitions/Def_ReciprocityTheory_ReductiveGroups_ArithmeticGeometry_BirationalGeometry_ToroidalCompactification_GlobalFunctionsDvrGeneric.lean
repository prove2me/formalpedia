-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:28.213877+00:00
-- url     : https://prove2.me/theorems/0cd6b9d9-d3f2-4339-a8b6-487368d7793e
-- title:
--   Global Functions Dvr Generic
-- statement:
--   Definitions and structural lemmas for Global Functions Dvr Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrGeneric.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
open ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric


