-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartProjIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartProjIndep
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:04.293802+00:00
-- url     : https://prove2.me/theorems/ac54252a-1ba6-5b5e-a1f5-7a802b965d3e
-- title:
--   PPts Pos Part Proj Indep
-- statement:
--   Definitions and structural lemmas for PPts Pos Part Proj Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsPosPartProjIndep.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensMeasurable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)
end GroundTheory.Heights₂.Heights


