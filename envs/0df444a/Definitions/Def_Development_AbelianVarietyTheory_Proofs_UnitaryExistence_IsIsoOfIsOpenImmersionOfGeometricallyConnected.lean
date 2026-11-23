-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:47.331839+00:00
-- url     : https://prove2.me/theorems/29832b39-7bf2-414a-b627-49ac6bcfb720
-- title:
--   Is Iso Of Is Open Immersion Of Geometrically Connected
-- statement:
--   Definitions and structural lemmas for Is Iso Of Is Open Immersion Of Geometrically Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIsoOfIsOpenImmersionOfGeometricallyConnected.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
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
namespace OpenSubgroupScheme
variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}
end OpenSubgroupScheme
end GlobalTheory


