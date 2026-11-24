-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordFibreDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordFibreDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:39:08.845382+00:00
-- url     : https://prove2.me/theorems/05017949-40fa-43e1-bc1e-ebb1449f7c33
-- title:
--   PCoord Fibre Deg
-- statement:
--   Definitions and structural lemmas for PCoord Fibre Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordFibreDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordFibreDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GenFibreChartDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
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
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
end GroundTheory.Heights₂.Heights.Targets


