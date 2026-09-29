-- Prove2me | solution 1 for AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d0c8ad86-3eca-5745-abca-5179c07b5dc2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] (f g : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g :
        Localization.Away f →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft g f :
        Localization.Away g →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) := by
  classical

  let Rg := Localization.Away g
  let T' := Localization.Away (algebraMap R Rg f)

  haveI hT' : IsLocalization.Away (f * g) T' := inferInstance

  let fm : Localization.Away f →+* T' :=
    IsLocalization.Away.lift f (g := algebraMap R T')
      (by
        have : IsUnit (algebraMap Rg T' (algebraMap R Rg f)) := IsLocalization.Away.algebraMap_isUnit _
        rwa [← IsScalarTower.algebraMap_apply] at this)
  have hfm : fm.comp (algebraMap R (Localization.Away f)) = (algebraMap Rg T').comp (algebraMap R Rg) := by
    rw [IsLocalization.Away.lift_comp]; exact (IsScalarTower.algebraMap_eq R Rg T')

  haveI : IsLocalization ((Submonoid.powers f).map (algebraMap R Rg)) T' := by
    rw [Submonoid.map_powers]; exact inferInstance
  have hpo := CommRingCat.isPushout_of_isLocalization (algebraMap R Rg) fm hfm (Submonoid.powers f)

  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip

  let e : Localization.Away (f * g) ≃ₐ[R] T' :=
    IsLocalization.algEquiv (Submonoid.powers (f * g)) (Localization.Away (f * g)) T'
  have h₁ : (IsLocalization.Away.awayToAwayRight f g : Localization.Away f →+* Localization.Away (f * g)) =
      e.symm.toAlgHom.toRingHom.comp fm := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.Away.awayToAwayRight_eq]
    rw [show fm (algebraMap R _ x) = algebraMap R T' x from IsLocalization.Away.lift_eq _ _ _]
    exact (e.symm.commutes x).symm
  have h₂ : (IsLocalization.Away.awayToAwayLeft g f : Localization.Away g →+* Localization.Away (f * g)) =
      e.symm.toAlgHom.toRingHom.comp (algebraMap Rg T') := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
    rw [← IsScalarTower.algebraMap_apply]
    exact (e.symm.commutes x).symm

  let ιIso : Spec (CommRingCat.of (Localization.Away (f * g))) ≅ Spec (CommRingCat.of T') :=
    Scheme.Spec.mapIso (e.symm.toRingEquiv.toCommRingCatIso).op
  have hι : ιIso.hom = Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) := rfl
  rw [h₁, h₂, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, ← hι]
  refine hpb.of_iso ιIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp

end S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft
end P2MW
export P2MW.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft (solution)
