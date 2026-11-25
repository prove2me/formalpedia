-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:06:44.191525+00:00
-- url     : https://prove2.me/theorems/da44ec53-ac7d-50e4-881d-42ecd3f05b19
-- title:
--   Is Grp Pullback Factor
-- statement:
--   Definitions and structural lemmas for Is Grp Pullback Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Hom
variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]
def preH {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) : (X ⟶ M) →* (Y ⟶ M) :=
  MonoidHom.mk' (f ≫ ·) fun a b => MonObj.comp_mul f a b
end Hom
section Push
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
def pushforwardHom : (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) :=
  MonoidHom.mk' (pushR G) fun a b => by
    show iotaB ≫ Geo.Tor.pushPt _ (a * b) = (iotaB ≫ Geo.Tor.pushPt _ a) * (iotaB ≫ Geo.Tor.pushPt _ b)
    rw [← MonObj.comp_mul]
    congr 1
    exact map_mul (Geo.Tor.pushHom (Geo.Tor.isGrpPullback_pullback G (fB R R')) _) a b
end Push
end ReciprocityTheory.ChartRestriction.G.Chart


