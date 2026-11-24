-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:20.5265+00:00
-- url     : https://prove2.me/theorems/f6037154-0bd6-4dd5-a80d-f9888e58e2fc
-- title:
--   Avoid Ring
-- statement:
--   Definitions and structural lemmas for Avoid Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean

import Mathlib
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
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.Inter.AvoidRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
end GroundTheory.Heights₂.Heights.Inter.AvoidRing


