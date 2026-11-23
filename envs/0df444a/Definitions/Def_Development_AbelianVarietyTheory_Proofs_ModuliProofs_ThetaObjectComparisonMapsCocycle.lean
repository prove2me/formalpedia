-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaObjectComparisonMapsCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:39.949361+00:00
-- url     : https://prove2.me/theorems/653e90c3-d35d-4c20-b8b5-9699a308a95b
-- title:
--   Theta Object Comparison Maps Cocycle
-- statement:
--   Definitions and structural lemmas for Theta Object Comparison Maps Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaObjectComparisonMapsCocycle.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ThetaCocycle
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
def PullsBack (t' : TObj g k J β s') (t : TObj g k J β s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧ ∀ l, (t'.pt l).left ≫ φ = f ≫ (t.pt l).left
end GlobalTheory.ThetaCocycle


