-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:33.685985+00:00
-- url     : https://prove2.me/theorems/347d57a8-9344-4ff7-8c5d-8ce5ad719268
-- title:
--   PLoc Ring Frac
-- statement:
--   Definitions and structural lemmas for PLoc Ring Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace LocRingFrac
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end LocRingFrac
end
end GroundTheory.Heights₂.Heights.Inter


