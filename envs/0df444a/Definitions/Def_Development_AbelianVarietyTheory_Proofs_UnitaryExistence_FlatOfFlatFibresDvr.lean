-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:51.219406+00:00
-- url     : https://prove2.me/theorems/0fddf28c-c366-41df-803b-4da366f39d2a
-- title:
--   Flat Of Flat Fibres Dvr
-- statement:
--   Definitions and structural lemmas for Flat Of Flat Fibres Dvr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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
open TensorProduct IsLocalRing
namespace GlobalTheory
namespace FibreFlat
section Algebra
variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]
end Algebra
def FlatOver {X Y S S' : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S' ⟶ S) : Prop :=
  ∀ ⦃W Z : Scheme.{0}⦄ (a : W ⟶ X) (b : W ⟶ Z) (j : Z ⟶ Y) (h : Z ⟶ S'),
    IsPullback a b f j → j ≫ g = h ≫ s → Flat b
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}
end FibreFlat
end GlobalTheory


