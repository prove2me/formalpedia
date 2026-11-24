-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetSimpleNull
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetSimpleNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:01.896467+00:00
-- url     : https://prove2.me/theorems/005cd45e-f2d0-4af1-902f-192e56c42885
-- title:
--   PPts Sheet Simple Null
-- statement:
--   Definitions and structural lemmas for PPts Sheet Simple Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSheetSimpleNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetSimpleNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsGenericCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt

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
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)
end GroundTheory.Heights₂.Heights


