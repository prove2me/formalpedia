-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:05.032203+00:00
-- url     : https://prove2.me/theorems/3f9ae59a-3805-4db5-8e02-c72812d7d11e
-- title:
--   Ker Is Multi Homog Ideal
-- statement:
--   Definitions and structural lemmas for Ker Is Multi Homog Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def tWeight [DecidableEq K] (k : K) : K → ℕ := fun k' => if k' = k then 1 else 0
end RegularityValuationCentre
end
end GroundTheory.Heights₂.Heights.Inter


