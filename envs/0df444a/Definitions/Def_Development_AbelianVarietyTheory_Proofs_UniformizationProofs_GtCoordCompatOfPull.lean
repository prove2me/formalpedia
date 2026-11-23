-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:40.879802+00:00
-- url     : https://prove2.me/theorems/444809c9-b5db-4a32-9669-de5b6f79edb8
-- title:
--   Gt Coord Compat Of Pull
-- statement:
--   Definitions and structural lemmas for Gt Coord Compat Of Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
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
namespace GlobalTheory
namespace LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem thickMap_fstG {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)
noncomputable def thickMapOver {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
      (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    rw [← Over.w (fstG I (e + 1) G), ← Over.w (fstG I e G), ← thickMap_fstG I e G]
    exact (Category.assoc _ _ _).symm)
end LevelCompat
end GlobalTheory


