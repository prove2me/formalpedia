-- Prove2me | solution 1 for AlgebraicGeometry.isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3fc7944a-0857-5236-b479-27d8d1794177

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {L : Type} [Field L] (A : ValuationSubring L)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀]
    (ι : A₀ →+* ↥A) (hι : Function.Injective ι)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hGI : GeometricallyIntegral
      (Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ (FractionRing A₀)))))) :
    IsIntegral ↑(Limits.pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap ↥A L)))) := by
  classical

  let K₀ := FractionRing A₀
  let i₀ : A₀ →+* K₀ := algebraMap A₀ K₀
  let jA : CommRingCat.of ↥A ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap ↥A L)

  have hinj : Function.Injective ((algebraMap ↥A L).comp ι) :=
    (show Function.Injective (algebraMap ↥A L) from Subtype.val_injective).comp hι
  have hunits : ∀ y : nonZeroDivisors A₀, IsUnit (((algebraMap ↥A L).comp ι) y) := by
    intro y
    apply IsUnit.mk0
    intro h0
    exact nonZeroDivisors.ne_zero y.2 (hinj (by rw [h0, map_zero]))
  let lam : K₀ →+* L := IsLocalization.lift (M := nonZeroDivisors A₀) (g := (algebraMap ↥A L).comp ι) hunits
  have hlam : lam.comp i₀ = (algebraMap ↥A L).comp ι := IsLocalization.lift_comp hunits

  have hbot : Spec.map jA ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom lam) ≫ Spec.map (CommRingCat.ofHom i₀) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change ((algebraMap ↥A L).comp ι) a = (lam.comp i₀) a
    rw [hlam]

  have hsqX : IsPullback (iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))) toBase toBase₀
      (Spec.map (CommRingCat.ofHom ι)) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ iso rfl hiso
    rw [Category.assoc, pullback.condition, ← Category.assoc, hiso]
  have hsqZ : IsPullback (pullback.fst toBase (Spec.map jA)) (pullback.snd toBase (Spec.map jA)) toBase (Spec.map jA) :=
    IsPullback.of_hasPullback _ _
  have hbig := hsqZ.paste_horiz hsqX
  rw [hbot] at hbig

  have hsq₀ : IsPullback (pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom i₀)))
      (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom i₀))) toBase₀ (Spec.map (CommRingCat.ofHom i₀)) :=
    IsPullback.of_hasPullback _ _
  let liftZ : pullback toBase (Spec.map jA) ⟶ pullback toBase₀ (Spec.map (CommRingCat.ofHom i₀)) :=
    pullback.lift (pullback.fst toBase (Spec.map jA) ≫ iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)))
      (pullback.snd toBase (Spec.map jA) ≫ Spec.map (CommRingCat.ofHom lam))
      (by rw [hbig.w, Category.assoc])
  have h1 : liftZ ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom i₀)) =
      pullback.fst toBase (Spec.map jA) ≫ iso.hom ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι)) :=
    pullback.lift_fst _ _ _
  have h2 : liftZ ≫ pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom i₀)) =
      pullback.snd toBase (Spec.map jA) ≫ Spec.map (CommRingCat.ofHom lam) :=
    pullback.lift_snd _ _ _
  have hbig' : IsPullback (liftZ ≫ pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom i₀)))
      (pullback.snd toBase (Spec.map jA)) toBase₀
      (Spec.map (CommRingCat.ofHom lam) ≫ Spec.map (CommRingCat.ofHom i₀)) := by
    rw [h1]; exact hbig
  have hsq : IsPullback liftZ (pullback.snd toBase (Spec.map jA))
      (pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom i₀))) (Spec.map (CommRingCat.ofHom lam)) :=
    hbig'.of_right h2 hsq₀

  exact hGI.geometrically_isIntegral (Spec.map (CommRingCat.ofHom lam)) liftZ (pullback.snd toBase (Spec.map jA)) hsq

end S_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_isIntegral_pullback_specMap_of_geometricallyIntegral_pullback_snd_of_iso_pullback (solution)
