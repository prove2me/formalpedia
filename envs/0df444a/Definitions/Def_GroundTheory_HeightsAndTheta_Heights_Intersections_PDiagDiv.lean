-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:31.668631+00:00
-- url     : https://prove2.me/theorems/8028ba35-7d5f-4b6c-b934-be2649028518
-- title:
--   PDiag Div
-- statement:
--   Definitions and structural lemmas for PDiag Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagDiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace DiagonalDivisor
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end DiagonalDivisor
end
end GroundTheory.Heights₂.Heights.Inter


