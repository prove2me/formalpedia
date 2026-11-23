-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:25.711984+00:00
-- url     : https://prove2.me/theorems/ec2271f7-868a-4d9c-a6b0-c2c6591fdcec
-- title:
--   Exists Is Closed Image Of Is Closed Subgroup
-- statement:
--   Definitions and structural lemmas for Exists Is Closed Image Of Is Closed Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
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
open Topology
namespace GlobalTheory
namespace RationalPoint
variable {k : Type} [Field k]
noncomputable def pt {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) : X.left :=
  y.left (IsLocalRing.closedPoint k)
@[reducible] noncomputable def zariski (X : Over (Sp k)) :
    TopologicalSpace (𝟙_ (Over (Sp k)) ⟶ X) :=
  TopologicalSpace.induced pt inferInstance
variable [IsAlgClosed k]
end RationalPoint
end GlobalTheory


