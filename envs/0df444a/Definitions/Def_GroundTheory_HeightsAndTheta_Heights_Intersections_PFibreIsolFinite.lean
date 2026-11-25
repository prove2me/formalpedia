-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreIsolFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreIsolFinite
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:09.411802+00:00
-- url     : https://prove2.me/theorems/23c8ab71-9a4a-5c86-a33e-7bcf4cec418f
-- title:
--   PFibre Isol Finite
-- statement:
--   Definitions and structural lemmas for PFibre Isol Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFibreIsolFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIsolFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace FibreIsolFinite
variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
end FibreIsolFinite
end GroundTheory.Heights₂.Heights.Inter


