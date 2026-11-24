-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:00.73554+00:00
-- url     : https://prove2.me/theorems/06e68aad-55a4-4308-b795-d1f58f4a2607
-- title:
--   Fun Field Le Loc Ring
-- statement:
--   Definitions and structural lemmas for Fun Field Le Loc Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/FunFieldLeLocRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
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
namespace RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
section Chain
variable [DecidableEq K] {E : Type*} [Field E]
def cS (E : Type*) [Field E] (S : Finset K) (k : K) : MvPolynomial K E :=
  if k ∈ S then 0 else MvPolynomial.X k
def specMap (ψ : MRing ι →+* E) (S : Finset K) : MRing ι →ₐ[ℤ] MvPolynomial K E :=
  aeval fun p => cS E S p.1 * MvPolynomial.C (ψ (X p))
end Chain
end RegularityFunctionFieldNumber
end
end GroundTheory.Heights₂.Heights.Inter


