-- Prove2me | solution 1 for AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/eb8d9920-f036-5b0d-b98f-249fc346fc8e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S K : Type u} [CommRing S] [CommRing K] (r : S →+* K)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    {AK : Scheme.{u}} (aK : AK ⟶ A) (xK : AK ⟶ Spec (CommRingCat.of K))
    (haK : IsPullback aK xK f (Spec.map (CommRingCat.ofHom r))) :
    ∃ (p₁ p₂ : pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ⟶ AK)
      (eK : Spec (CommRingCat.of K) ⟶ AK)
      (iX iY : AK ⟶ pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))),
      p₁ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.fst f f ∧
      p₁ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      p₂ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.snd f f ∧
      p₂ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      IsPullback p₁ p₂ xK xK ∧
      eK ≫ aK = Spec.map (CommRingCat.ofHom r) ≫ e ∧ eK ≫ xK = 𝟙 _ ∧
      IsClosedImmersion iX ∧ iX ≫ p₁ = 𝟙 AK ∧ iX ≫ p₂ = xK ≫ eK ∧
      iX ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (𝟙 A) (f ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ∧
      IsClosedImmersion iY ∧ iY ≫ p₁ = xK ≫ eK ∧ iY ≫ p₂ = 𝟙 AK ∧
      iY ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (f ≫ e) (𝟙 A) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by

  let σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom r)
  let qP : pullback f f ⟶ Spec (CommRingCat.of S) := pullback.fst f f ≫ f
  let πP := pullback.fst qP σ
  let πK := pullback.snd qP σ
  have hσ : Spec.map (CommRingCat.ofHom r) = σ := rfl

  have w₁ : (πP ≫ pullback.fst f f) ≫ f = πK ≫ σ := by
    rw [Category.assoc]; exact pullback.condition
  have w₂ : (πP ≫ pullback.snd f f) ≫ f = πK ≫ σ := by
    rw [Category.assoc, ← pullback.condition]; exact pullback.condition
  let p₁ : pullback qP σ ⟶ AK := haK.lift (πP ≫ pullback.fst f f) πK w₁
  let p₂ : pullback qP σ ⟶ AK := haK.lift (πP ≫ pullback.snd f f) πK w₂
  have hp₁a : p₁ ≫ aK = πP ≫ pullback.fst f f := haK.lift_fst _ _ _
  have hp₁x : p₁ ≫ xK = πK := haK.lift_snd _ _ _
  have hp₂a : p₂ ≫ aK = πP ≫ pullback.snd f f := haK.lift_fst _ _ _
  have hp₂x : p₂ ≫ xK = πK := haK.lift_snd _ _ _

  have hL : IsPullback πP p₁ (pullback.fst f f) aK := by
    refine (IsPullback.paste_vert_iff haK hp₁a.symm).mp ?_
    rw [hp₁x]
    exact IsPullback.of_hasPullback qP σ

  have hM : IsPullback (πP ≫ pullback.snd f f) p₁ f (aK ≫ f) :=
    IsPullback.paste_horiz hL (IsPullback.of_hasPullback f f).flip

  have hP : IsPullback p₁ p₂ xK xK := by
    have hM' : IsPullback (p₂ ≫ aK) p₁ f (xK ≫ Spec.map (CommRingCat.ofHom r)) := by
      rw [hp₂a, ← haK.w]; exact hM
    exact ((IsPullback.paste_horiz_iff haK (by rw [hp₁x, hp₂x])).mp hM').flip

  haveI : IsSeparated xK := MorphismProperty.of_isPullback haK inferInstance
  haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
  haveI : IsSeparated p₂ := MorphismProperty.of_isPullback hP inferInstance

  have we : (Spec.map (CommRingCat.ofHom r) ≫ e) ≫ f = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom r) := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  let eK : Spec (CommRingCat.of K) ⟶ AK := haK.lift (Spec.map (CommRingCat.ofHom r) ≫ e) (𝟙 _) we
  have heKa : eK ≫ aK = Spec.map (CommRingCat.ofHom r) ≫ e := haK.lift_fst _ _ _
  have heKx : eK ≫ xK = 𝟙 _ := haK.lift_snd _ _ _

  have wX : 𝟙 AK ≫ xK = (xK ≫ eK) ≫ xK := by rw [Category.assoc, heKx, Category.comp_id, Category.id_comp]
  have wY : (xK ≫ eK) ≫ xK = 𝟙 AK ≫ xK := wX.symm
  let iX : AK ⟶ pullback qP σ := hP.lift (𝟙 AK) (xK ≫ eK) wX
  let iY : AK ⟶ pullback qP σ := hP.lift (xK ≫ eK) (𝟙 AK) wY
  have hiX₁ : iX ≫ p₁ = 𝟙 AK := hP.lift_fst _ _ _
  have hiX₂ : iX ≫ p₂ = xK ≫ eK := hP.lift_snd _ _ _
  have hiY₁ : iY ≫ p₁ = xK ≫ eK := hP.lift_fst _ _ _
  have hiY₂ : iY ≫ p₂ = 𝟙 AK := hP.lift_snd _ _ _
  have hiXc : IsClosedImmersion iX := by
    haveI : IsClosedImmersion (iX ≫ p₁) := by rw [hiX₁]; infer_instance
    exact IsClosedImmersion.of_comp iX p₁
  have hiYc : IsClosedImmersion iY := by
    haveI : IsClosedImmersion (iY ≫ p₂) := by rw [hiY₂]; infer_instance
    exact IsClosedImmersion.of_comp iY p₂

  have hslX : iX ≫ πP = aK ≫ pullback.lift (𝟙 A) (f ≫ e)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id, ← hp₁a, ← Category.assoc, hiX₁,
        Category.id_comp]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← hp₂a, ← Category.assoc, hiX₂, Category.assoc, heKa,
        ← Category.assoc, ← haK.w, Category.assoc]
  have hslY : iY ≫ πP = aK ≫ pullback.lift (f ≫ e) (𝟙 A)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← hp₁a, ← Category.assoc, hiY₁, Category.assoc, heKa,
        ← Category.assoc, ← haK.w, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.comp_id, ← hp₂a, ← Category.assoc, hiY₂,
        Category.id_comp]
  exact ⟨p₁, p₂, eK, iX, iY, hp₁a, hp₁x, hp₂a, hp₂x, hP, heKa, heKx, hiXc, hiX₁, hiX₂, hslX, hiYc, hiY₁, hiY₂, hslY⟩

end S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section (solution)
