-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrdOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:29.054825+00:00
-- url     : https://prove2.me/theorems/93bbbd00-5184-45e8-a3f6-cd79c88c63ce
-- title:
--   PDiag Ord One
-- statement:
--   Definitions and structural lemmas for PDiag Ord One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOrdOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
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
namespace DiagonalOrderOne
section Length
variable {A : Type*} [CommRing A]
end Length
section Graded
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
end Graded
end DiagonalOrderOne
end
end GroundTheory.Heights₂.Heights.Inter


