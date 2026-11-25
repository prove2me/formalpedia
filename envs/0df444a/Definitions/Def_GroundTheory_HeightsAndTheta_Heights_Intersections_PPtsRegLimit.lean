-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:58:56.242649+00:00
-- url     : https://prove2.me/theorems/5e63b9e8-40c5-4a66-bfb5-914a13c553be
-- title:
--   PPts Reg Limit
-- statement:
--   Definitions and structural lemmas for PPts Reg Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsRegLimit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
end GroundTheory.Heights₂.Heights.Inter


