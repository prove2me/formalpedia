-- Prove2me | solution 1 for AlgebraicGeometry.isPullback_pullback_lift_morphismRestrict_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/639f1d12-a981-5ff0-814f-4e1956994a15

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
    (Y₁ Y₂ : Scheme.{u}) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
    (g₁ : (↑U₁ : Scheme.{u}) ⟶ Y₁) (g₂ : (↑U₂ : Scheme.{u}) ⟶ Y₂)
    (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
    (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π))) :
    IsPullback (pullback.lift
        ((pullback f₀ f₀).homOfLE (inf_le_left : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁)
        ((pullback f₀ f₀).homOfLE (inf_le_right : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂)
        (by simp only [Category.assoc]; rw [hg₁.w, hg₂.w];
            simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]) :
        (↑(pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) : Scheme.{u}) ⟶ pullback q₁ q₂)
      ((pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂).ι ≫ pullback.fst f₀ f₀ ≫ f₀)
      (pullback.fst q₁ q₂ ≫ q₁) (Spec.map (CommRingCat.ofHom π)) := by

  set W₀ : (pullback f₀ f₀).Opens := pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ with hW₀
  set a₁ : (↑W₀ : Scheme.{u}) ⟶ ↑U₁ := (pullback f₀ f₀).homOfLE (inf_le_left : W₀ ≤ _) ≫ (pullback.fst f₀ f₀ ∣_ U₁) with ha₁
  set a₂ : (↑W₀ : Scheme.{u}) ⟶ ↑U₂ := (pullback f₀ f₀).homOfLE (inf_le_right : W₀ ≤ _) ≫ (pullback.snd f₀ f₀ ∣_ U₂) with ha₂
  have ha₁ι : a₁ ≫ U₁.ι = W₀.ι ≫ pullback.fst f₀ f₀ := by
    rw [ha₁, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have ha₂ι : a₂ ≫ U₂.ι = W₀.ι ≫ pullback.snd f₀ f₀ := by
    rw [ha₂, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

  have hW : IsPullback a₁ a₂ (U₁.ι ≫ f₀) (U₂.ι ≫ f₀) := by
    have hP : IsPullback (pullback.fst f₀ f₀) (pullback.snd f₀ f₀) f₀ f₀ := IsPullback.of_hasPullback f₀ f₀
    have sB := (isPullback_morphismRestrict (pullback.fst f₀ f₀) U₁).paste_vert hP

    have sC := ((isPullback_morphismRestrict ((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) U₂).paste_vert
      sB.flip).flip

    have hVimg : (pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ''ᵁ (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ⁻¹ᵁ U₂) = W₀ := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    let e : (↑(((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ⁻¹ᵁ U₂) : Scheme.{u}) ≅ ↑W₀ :=
      (pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι.isoImage _ ≪≫ (pullback f₀ f₀).isoOfEq hVimg
    have he : e.hom ≫ W₀.ι = (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ⁻¹ᵁ U₂).ι ≫ (pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι := by
      simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
    have he' : e.inv ≫ (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ⁻¹ᵁ U₂).ι ≫ (pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι = W₀.ι := by
      rw [← he, Iso.inv_hom_id_assoc]
    have h1 : e.inv ≫ (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ⁻¹ᵁ U₂).ι ≫ (pullback.fst f₀ f₀ ∣_ U₁) = a₁ := by
      rw [← cancel_mono U₁.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ha₁ι, ← he']
      simp only [Category.assoc]
    have h2 : e.inv ≫ (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ∣_ U₂) = a₂ := by
      rw [← cancel_mono U₂.ι, Category.assoc,
        morphismRestrict_ι ((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) U₂, ha₂ι, ← he']
      simp only [Category.assoc]
    have s : IsPullback e.inv (e.inv ≫ (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ∣_ U₂))
        (((pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι ≫ pullback.snd f₀ f₀) ∣_ U₂) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    have := s.paste_horiz sC
    rw [Category.id_comp, h1, h2] at this
    exact this

  have hrect : IsPullback (a₂ ≫ g₂) a₁ q₂ (g₁ ≫ q₁) := by
    have t := hW.paste_vert hg₂.flip

    rw [hg₁.w]
    exact t.flip

  set G₀ := (pullback.lift
        ((pullback f₀ f₀).homOfLE (inf_le_left : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁)
        ((pullback f₀ f₀).homOfLE (inf_le_right : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂)
        (by simp only [Category.assoc]; rw [hg₁.w, hg₂.w];
            simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]) :
        (↑(pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) : Scheme.{u}) ⟶ pullback q₁ q₂) with hG₀
  have hGa : G₀ ≫ pullback.fst q₁ q₂ = a₁ ≫ g₁ := by rw [ha₁, Category.assoc]; exact pullback.lift_fst _ _ _
  have hGb : G₀ ≫ pullback.snd q₁ q₂ = a₂ ≫ g₂ := by rw [ha₂, Category.assoc]; exact pullback.lift_snd _ _ _
  have htop : IsPullback G₀ a₁ (pullback.fst q₁ q₂) g₁ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd q₁ q₂) (v₁₃ := q₂) (h₂₂ := q₁) ?_ hGa
      (IsPullback.of_hasPullback q₁ q₂).flip
    rw [hGb]
    exact hrect

  have := htop.paste_vert hg₁
  rw [← Category.assoc, ha₁ι, Category.assoc] at this
  exact this

end S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback (solution)
