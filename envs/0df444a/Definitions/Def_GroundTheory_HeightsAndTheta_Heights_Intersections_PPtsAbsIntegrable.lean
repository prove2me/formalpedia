-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAbsIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAbsIntegrable
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:17.739802+00:00
-- url     : https://prove2.me/theorems/3d8d9ee0-cdb0-4f26-8554-acb889bf3c5c
-- title:
--   PPts Abs Integrable
-- statement:
--   Definitions and structural lemmas for PPts Abs Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAbsIntegrable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
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
open scoped ComplexOrder
namespace PointsAbsIntegrable
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end PointsAbsIntegrable
end GroundTheory.Heights₂.Heights.Inter


