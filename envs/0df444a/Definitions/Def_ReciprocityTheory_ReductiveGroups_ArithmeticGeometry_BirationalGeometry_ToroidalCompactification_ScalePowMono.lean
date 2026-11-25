-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:37.365981+00:00
-- url     : https://prove2.me/theorems/0b689a7d-76eb-4bef-8392-239d5d021927
-- title:
--   Scale Pow Mono
-- statement:
--   Definitions and structural lemmas for Scale Pow Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
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
section Maps
variable {S : Type} [CommRing S]
def awayHom (u : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u)) :
    Localization.Away u →ₐ[S] B :=
  { IsLocalization.Away.lift u hu with commutes' := fun r => IsLocalization.Away.lift_eq u hu r }
def qHom (u v : S) (B : Type) [CommRing B] [Algebra S B] (hu : IsUnit (algebraMap S B u))
    (hv : IsUnit (algebraMap S B v)) : Qv u v →ₐ[S] B :=
  { IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) (g := (awayHom u B hu).toRingHom)
      (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hv) with
    commutes' := fun r => by
      show IsLocalization.Away.lift (algebraMap S (Localization.Away u) v) _
        (algebraMap (Localization.Away u) (Qv u v) (algebraMap S (Localization.Away u) r)) = algebraMap S B r
      rw [IsLocalization.Away.lift_eq]
      exact (awayHom u B hu).commutes r }
end Maps
section Extend
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable [∀ s : S, Smooth (Gs G s).hom]
end Extend
end ReciprocityTheory.ChartRestriction.G.Chart


