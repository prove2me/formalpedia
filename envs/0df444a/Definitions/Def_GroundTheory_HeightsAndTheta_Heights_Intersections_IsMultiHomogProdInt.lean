-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogProdInt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogProdInt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:15.977725+00:00
-- url     : https://prove2.me/theorems/5cd274d1-7e71-58d0-b38b-c343835ac211
-- title:
--   Is Multi Homog Prod Int
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Prod Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogProdInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
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
namespace GenericPointsAvoidBadLocus
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
end GenericPointsAvoidBadLocus
end GroundTheory.Heights₂.Heights.Inter


