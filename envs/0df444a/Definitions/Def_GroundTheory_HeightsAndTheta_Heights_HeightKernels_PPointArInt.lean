-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:25:57.157954+00:00
-- url     : https://prove2.me/theorems/ba20bb6f-5413-5349-9d87-3b65982f39d0
-- title:
--   PPoint Ar Int
-- statement:
--   Definitions and structural lemmas for PPoint Ar Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPointArInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
namespace PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
variable {K' : Type} [Field K'] [NumberField K']
end PointArithIntersection
end
end GroundTheory.Heights₂.Heights


