-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:35.891501+00:00
-- url     : https://prove2.me/theorems/3d396b5b-5f52-4aec-b9bd-df61f7c12255
-- title:
--   PDe Le Semi Pos
-- statement:
--   Definitions and structural lemmas for PDe Le Semi Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDeLeSemiPos.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsMonoSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end GroundTheory.Heights₂.Heights.Inter


