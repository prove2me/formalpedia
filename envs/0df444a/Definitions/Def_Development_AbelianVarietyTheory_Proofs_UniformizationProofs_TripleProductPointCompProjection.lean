-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:42.979798+00:00
-- url     : https://prove2.me/theorems/ebf3d2d7-b5b4-4722-ad98-094d16934e14
-- title:
--   Triple Product Point Comp Projection
-- statement:
--   Definitions and structural lemmas for Triple Product Point Comp Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Cube
variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))
abbrev tri : T.left ⟶ (G3 G).left :=
  (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p))).left
end Cube
end WCub
end GlobalTheory


