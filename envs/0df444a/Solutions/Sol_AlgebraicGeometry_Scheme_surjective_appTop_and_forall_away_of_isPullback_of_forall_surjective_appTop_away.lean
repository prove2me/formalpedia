-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/661e8457-c854-5e29-a084-449e2e4afd85

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace C7HG

theorem surj_appTop_of_isPullback_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (r : S) (B : Type u) [CommRing B] [Algebra S B] [IsLocalization.Away r B]
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) :
    Function.Surjective (f'.appTop).hom := by
  classical
  let L := Localization.Away r

  let ε : L ≃ₐ[S] B := IsLocalization.algEquiv (Submonoid.powers r) L B
  have hε : (ε.toAlgHom.toRingHom).comp (algebraMap S L) = algebraMap S B := ε.toAlgHom.comp_algebraMap
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      Spec.map (CommRingCat.ofHom ε.toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S L)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]

  let ιε : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of L) := Scheme.Spec.mapIso (ε.toRingEquiv.toCommRingCatIso).op
  have hιε : ιε.hom = Spec.map (CommRingCat.ofHom ε.toAlgHom.toRingHom) := rfl

  have hsq : IsPullback g (f' ≫ ιε.hom) f (Spec.map (CommRingCat.ofHom (algebraMap S L))) := by
    have := hg
    rw [hSpec, ← hιε] at this

    refine IsPullback.of_iso this (Iso.refl _) (Iso.refl _) ιε (Iso.refl _) (by simp) (by simp) (by simp) (by simp [hιε])
  let P₀ := pullback f (Spec.map (CommRingCat.ofHom (algebraMap S L)))
  let θ : A' ≅ P₀ := hsq.isoPullback
  have hθ : θ.hom ≫ pullback.snd _ _ = f' ≫ ιε.hom := hsq.isoPullback_hom_snd

  have h1 : Function.Surjective ((θ.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S L)))).appTop).hom := by
    rw [Scheme.Hom.comp_appTop]
    show Function.Surjective ((θ.hom.appTop).hom ∘ (pullback.snd f _).appTop.hom)
    haveI : IsIso θ.hom.appTop := by
      rw [← Scheme.Γ_map_op]
      exact Functor.map_isIso Scheme.Γ θ.op.hom
    exact (ConcreteCategory.bijective_of_isIso θ.hom.appTop).2.comp (hΓ r)
  rw [hθ, Scheme.Hom.comp_appTop] at h1
  exact Function.Surjective.of_comp h1

end C7HG

open C7HG in
theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hΓ : ∀ r : S, Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
    (r : S) (B : Type u) [CommRing B] [Algebra S B] [IsLocalization.Away r B]
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) :
    Function.Surjective (f'.appTop).hom ∧
      ∀ r' : B, Function.Surjective
        ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))))).appTop).hom := by
  classical
  refine ⟨surj_appTop_of_isPullback_away f hΓ r B f' g hg, fun r' => ?_⟩

  let T := Localization.Away r'
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (S := B) r'

  have hu : IsUnit (algebraMap B T (algebraMap S B (r ^ n))) := by
    rw [map_pow, map_pow]
    exact (((IsLocalization.Away.algebraMap_isUnit (S := B) r).map (algebraMap B T)).pow n)
  haveI : IsLocalization.Away (algebraMap S B s) T := by
    rw [← hs]
    exact IsLocalization.Away.mul_of_isUnit r' _ hu
  haveI : IsLocalization.Away (s * r) T := IsLocalization.Away.mul B T r s

  have hsq : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom (algebraMap B T))) ≫ g)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap B T)))) f
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    have := (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom (algebraMap B T)))).paste_horiz hg
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq S B T] at this
  exact surj_appTop_of_isPullback_away f hΓ (s * r) T _ _ hsq

end S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away (solution)
