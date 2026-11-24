-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:09.959201+00:00
-- url     : https://prove2.me/theorems/8093036c-9720-4cd2-bf89-4ae901055db1
-- title:
--   PChoice
-- statement:
--   Definitions and structural lemmas for PChoice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
end Choice
end GroundTheory.Heights₂.Heights.Inter


