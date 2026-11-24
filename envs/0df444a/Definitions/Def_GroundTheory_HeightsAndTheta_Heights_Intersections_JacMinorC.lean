-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:52.984963+00:00
-- url     : https://prove2.me/theorems/2416d6c0-1593-46e7-8b9c-091e388a4c85
-- title:
--   Jac Minor C
-- statement:
--   Definitions and structural lemmas for Jac Minor C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/JacMinorC.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
section Minors
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type} [CommRing R]
end Minors
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


