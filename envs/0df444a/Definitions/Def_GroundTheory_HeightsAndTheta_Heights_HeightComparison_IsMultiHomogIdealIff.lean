-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:45.721242+00:00
-- url     : https://prove2.me/theorems/d3e32b0d-1b00-48f1-b08f-a78ad0356929
-- title:
--   Is Multi Homog Ideal Iff
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Ideal Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
section Homog
variable [DecidableEq K] [∀ k, Fintype (ι k)]
end Homog
section Ideals
variable [DecidableEq K] [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Ideals
section Cycles
end Cycles
end
end GroundTheory.Heights₂.Heights.Bridge


