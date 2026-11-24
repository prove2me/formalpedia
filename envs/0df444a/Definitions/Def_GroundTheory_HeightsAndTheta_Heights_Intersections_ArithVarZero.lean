-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:56.846779+00:00
-- url     : https://prove2.me/theorems/3754da81-1f56-464f-aa2a-744c0ae5dafc
-- title:
--   Arith Var Zero
-- statement:
--   Definitions and structural lemmas for Arith Var Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArithVarZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def killBlocks (S : Set K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p
end GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


