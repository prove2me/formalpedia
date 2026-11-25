-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsNormalise
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsNormalise
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:15.351634+00:00
-- url     : https://prove2.me/theorems/1c05cd15-d049-5700-8149-de1adaff60c4
-- title:
--   Exists Normalise
-- statement:
--   Definitions and structural lemmas for Exists Normalise, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsNormalise.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GenericPointsInAffineChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
end GenericPointsInAffineChart
end GroundTheory.Heights₂.Heights.Inter


