-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:18.900536+00:00
-- url     : https://prove2.me/theorems/6e8e970a-829e-42db-8750-78c7744b5ea0
-- title:
--   PLoc Ring Pow
-- statement:
--   Definitions and structural lemmas for PLoc Ring Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
namespace LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical in

def multiDegWeight (ι : K → Type*) : (Σ k, ι k) → (K → ℕ) := fun p k => if p.1 = k then 1 else 0
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end LocRingPow
end
end GroundTheory.Heights₂.Heights.Inter


