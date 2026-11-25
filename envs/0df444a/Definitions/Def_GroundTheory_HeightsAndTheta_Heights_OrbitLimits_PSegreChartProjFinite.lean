-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:05.919329+00:00
-- url     : https://prove2.me/theorems/065bdc54-7763-54e6-96ce-7d4b24d6e2fd
-- title:
--   PSegre Chart Proj Finite
-- statement:
--   Definitions and structural lemmas for PSegre Chart Proj Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix
end GroundTheory.Heights₂.Heights


