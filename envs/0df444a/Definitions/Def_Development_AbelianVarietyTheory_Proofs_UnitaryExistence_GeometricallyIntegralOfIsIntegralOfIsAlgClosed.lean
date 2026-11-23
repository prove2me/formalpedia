-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:27.116037+00:00
-- url     : https://prove2.me/theorems/b568fea9-6197-4579-8687-3dd9c91112c4
-- title:
--   Geometrically Integral Of Is Integral Of Is Alg Closed
-- statement:
--   Definitions and structural lemmas for Geometrically Integral Of Is Integral Of Is Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeometricallyIntegralOfIsIntegralOfIsAlgClosed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
namespace GlobalTheory
universe u
end GlobalTheory


