-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldExistsInv
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldExistsInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:06.104357+00:00
-- url     : https://prove2.me/theorems/9d1fbd51-f813-498b-bb54-bf9f5999bf0d
-- title:
--   Fun Field Exists Inv
-- statement:
--   Definitions and structural lemmas for Fun Field Exists Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldExistsInv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeOfHeightMapEqZero
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end
end GroundTheory.Heights₂.Heights.Inter


