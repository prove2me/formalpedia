-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:58.089998+00:00
-- url     : https://prove2.me/theorems/643306ee-c72a-4687-b2e8-087f0ba62a50
-- title:
--   Exists Grp Obj Of Flat Closed
-- statement:
--   Definitions and structural lemmas for Exists Grp Obj Of Flat Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsGrpObjOfFlatClosed.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
section
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
end
end GlobalTheory


