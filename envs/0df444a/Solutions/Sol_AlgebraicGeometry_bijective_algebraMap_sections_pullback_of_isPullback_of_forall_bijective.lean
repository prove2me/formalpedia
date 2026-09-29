-- Prove2me | solution 1 for AlgebraicGeometry.bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/549f04ee-816c-58a8-a280-09893d9fee2c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (S' : Type u) [CommRing S'] [Algebra S S'] {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (T : Type u) [CommRing T] [Algebra S' T] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)) ⊤
    Function.Bijective (algebraMap T Γ(pullback f' (Scheme.TwoAffineOpenCover.specMap S' T), ⊤)) := by
  classical

  letI algST : Algebra S T := ((algebraMap S' T).comp (algebraMap S S')).toAlgebra
  have hST : algebraMap S T = (algebraMap S' T).comp (algebraMap S S') := rfl

  have hbot : Scheme.TwoAffineOpenCover.specMap S' T ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) =
      Scheme.TwoAffineOpenCover.specMap S T := by
    change Spec.map (CommRingCat.ofHom (algebraMap S' T)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) =
      Spec.map (CommRingCat.ofHom (algebraMap S T))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hST]
  have hbig : IsPullback (pullback.fst f' (Scheme.TwoAffineOpenCover.specMap S' T) ≫ g)
      (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)) f (Scheme.TwoAffineOpenCover.specMap S T) := by
    rw [← hbot]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback f' (Scheme.TwoAffineOpenCover.specMap S' T)) hg
  let κ := hbig.isoPullback
  have hκ : κ.hom ≫ pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T) =
      pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T) := hbig.isoPullback_hom_snd

  have h0 := hH0 T
  letI i1 := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
  letI i2 := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)) ⊤
  have hfac : (algebraMap T Γ(pullback f' (Scheme.TwoAffineOpenCover.specMap S' T), ⊤) : T → _) =
      (κ.hom.appLE ⊤ ⊤ le_top).hom ∘ (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)) := by
    change (((Scheme.ΓSpecIso (.of T)).inv ≫ (pullback.snd f' (Scheme.TwoAffineOpenCover.specMap S' T)).appLE ⊤ ⊤ le_top).hom : T → _) =
      (κ.hom.appLE ⊤ ⊤ le_top).hom ∘ ((Scheme.ΓSpecIso (.of T)).inv ≫ (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)).appLE ⊤ ⊤ le_top).hom
    rw [← hκ, ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ ⊤ le_top le_top]
    rfl

  have happ : κ.hom.appLE ⊤ ⊤ le_top = κ.hom.appTop := Scheme.Hom.appLE_eq_app _
  have e1 : κ.hom.appTop ≫ κ.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  have e2 : κ.inv.appTop ≫ κ.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  let ι : Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤) ≅ Γ(pullback f' (Scheme.TwoAffineOpenCover.specMap S' T), ⊤) :=
    ⟨κ.hom.appTop, κ.inv.appTop, e1, e2⟩
  have hbijκ : Function.Bijective (κ.hom.appLE ⊤ ⊤ le_top).hom := by
    rw [happ]
    haveI : IsIso ι.hom := ι.isIso_hom
    exact ConcreteCategory.bijective_of_isIso ι.hom
  rw [hfac]
  exact hbijκ.comp h0

end S_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective (solution)
