-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsPullOne
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsPullOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:51.900944+00:00
-- url     : https://prove2.me/theorems/d4336f69-f2e9-46dd-89f0-518c5f2de700
-- title:
--   Expands Pull One
-- statement:
--   Definitions and structural lemmas for Expands Pull One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsPullOne.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
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
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end ReciprocityTheory.ChartRestriction.G.DVR


