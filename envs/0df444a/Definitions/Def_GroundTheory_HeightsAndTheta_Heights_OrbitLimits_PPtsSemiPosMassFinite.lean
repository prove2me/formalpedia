-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSemiPosMassFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSemiPosMassFinite
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:00.563925+00:00
-- url     : https://prove2.me/theorems/fbb27b47-bb34-5660-b78b-1e22cf9da58f
-- title:
--   PPts Semi Pos Mass Finite
-- statement:
--   Definitions and structural lemmas for PPts Semi Pos Mass Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsSemiPosMassFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSemiPosMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChartFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
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
open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)
namespace PtsSemiPosMassFinite
end PtsSemiPosMassFinite
end GroundTheory.Heights₂.Heights


