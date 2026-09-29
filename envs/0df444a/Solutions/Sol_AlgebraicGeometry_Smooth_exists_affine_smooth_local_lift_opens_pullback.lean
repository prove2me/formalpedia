-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_affine_smooth_local_lift_opens_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6389e617-5722-5700-aff9-4e04d15688d6

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
    (Y₁ Y₂ : Scheme.{u}) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
    (hq₁ : Smooth q₁) (hq₂ : Smooth q₂)
    (g₁ : (↑U₁ : Scheme.{u}) ⟶ Y₁) (g₂ : (↑U₂ : Scheme.{u}) ⟶ Y₂)
    (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
    (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π)))
    (V : (pullback f₀ f₀).Opens) (hVaff : IsAffineOpen V)
    (hV₁ : V ≤ pullback.fst f₀ f₀ ⁻¹ᵁ U₁) (hV₂ : V ≤ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) :
    ∃ (Z : Scheme.{u}) (qZ : Z ⟶ Spec (CommRingCat.of T')) (_ : IsAffine Z) (_ : Smooth qZ)
      (gZ : (↑V : Scheme.{u}) ⟶ Z)
      (_ : IsPullback gZ (V.ι ≫ pullback.fst f₀ f₀ ≫ f₀) qZ (Spec.map (CommRingCat.ofHom π)))
      (h₁ : Z ⟶ Y₁) (h₂ : Z ⟶ Y₂),
      (h₁ ≫ q₁ = qZ ∧ gZ ≫ h₁ = (pullback f₀ f₀).homOfLE hV₁ ≫ (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁) ∧
      (h₂ ≫ q₂ = qZ ∧ gZ ≫ h₂ = (pullback f₀ f₀).homOfLE hV₂ ≫ (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂) := by
  classical
  haveI := hq₁; haveI := hq₂
  have hcart := AlgebraicGeometry.isPullback_pullback_lift_morphismRestrict_of_isPullback π f₀ U₁ U₂ Y₁ Y₂ q₁ q₂ g₁ g₂ hg₁ hg₂
  set W₀ : (pullback f₀ f₀).Opens := pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ with hW₀
  set G₀ := (pullback.lift
        ((pullback f₀ f₀).homOfLE (inf_le_left : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁)
        ((pullback f₀ f₀).homOfLE (inf_le_right : pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂ ≤ _) ≫
          (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂)
        (by simp only [Category.assoc]; rw [hg₁.w, hg₂.w];
            simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]) :
        (↑(pullback.fst f₀ f₀ ⁻¹ᵁ U₁ ⊓ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) : Scheme.{u}) ⟶ pullback q₁ q₂) with hG₀
  have hG₁ : G₀ ≫ pullback.fst q₁ q₂ = (pullback f₀ f₀).homOfLE inf_le_left ≫ (pullback.fst f₀ f₀ ∣_ U₁) ≫ g₁ :=
    pullback.lift_fst _ _ _
  have hG₂ : G₀ ≫ pullback.snd q₁ q₂ = (pullback f₀ f₀).homOfLE inf_le_right ≫ (pullback.snd f₀ f₀ ∣_ U₂) ≫ g₂ :=
    pullback.lift_snd _ _ _
  have hVW : V ≤ W₀ := le_inf hV₁ hV₂

  let V' : (↑W₀ : Scheme.{u}).Opens := W₀.ι ⁻¹ᵁ V
  have hrange : Set.range (V'.ι ≫ W₀.ι).base = Set.range V.ι.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    change W₀.ι.base '' (W₀.ι.base ⁻¹' (V : Set _)) = (V : Set _)
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.mpr hVW
  let e : (↑V' : Scheme.{u}) ≅ ↑V := IsOpenImmersion.isoOfRangeEq (V'.ι ≫ W₀.ι) V.ι hrange
  have he : e.hom ≫ V.ι = V'.ι ≫ W₀.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' : e.inv ≫ V'.ι ≫ W₀.ι = V.ι := by rw [← he, Iso.inv_hom_id_assoc]
  haveI : IsAffine (↑V : Scheme.{u}) := hVaff
  have hV'aff : IsAffineOpen V' := IsAffine.of_isIso e.hom
  obtain ⟨Z, hZaff, γ, hγ, hγc⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent π hπ hker
      (pullback.fst q₁ q₂ ≫ q₁) (W₀.ι ≫ pullback.fst f₀ f₀ ≫ f₀) G₀ hcart V' hV'aff

  have hsq : IsPullback (e.inv ≫ γ) (V.ι ≫ pullback.fst f₀ f₀ ≫ f₀) (Z.ι ≫ pullback.fst q₁ q₂ ≫ q₁)
      (Spec.map (CommRingCat.ofHom π)) := by
    have s : IsPullback e.inv (V.ι ≫ pullback.fst f₀ f₀ ≫ f₀) (V'.ι ≫ W₀.ι ≫ pullback.fst f₀ f₀ ≫ f₀) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← he']; simp only [Category.assoc]⟩
    have := s.paste_horiz hγc
    rwa [Category.id_comp] at this

  have hl : e.inv ≫ V'.ι ≫ (pullback f₀ f₀).homOfLE (inf_le_left : W₀ ≤ pullback.fst f₀ f₀ ⁻¹ᵁ U₁) =
      (pullback f₀ f₀).homOfLE hV₁ := by
    rw [← cancel_mono (pullback.fst f₀ f₀ ⁻¹ᵁ U₁).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact he'
  have hr : e.inv ≫ V'.ι ≫ (pullback f₀ f₀).homOfLE (inf_le_right : W₀ ≤ pullback.snd f₀ f₀ ⁻¹ᵁ U₂) =
      (pullback f₀ f₀).homOfLE hV₂ := by
    rw [← cancel_mono (pullback.snd f₀ f₀ ⁻¹ᵁ U₂).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι]
    exact he'
  haveI : IsAffine (↑Z : Scheme.{u}) := hZaff
  refine ⟨↑Z, Z.ι ≫ pullback.fst q₁ q₂ ≫ q₁, hZaff, inferInstance, e.inv ≫ γ, hsq,
    Z.ι ≫ pullback.fst q₁ q₂, Z.ι ≫ pullback.snd q₁ q₂, ⟨rfl, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Category.assoc, ← Category.assoc γ, hγ, Category.assoc, hG₁, ← hl]
    simp only [Category.assoc]
  · simp only [Category.assoc, pullback.condition]
  · rw [Category.assoc, ← Category.assoc γ, hγ, Category.assoc, hG₂, ← hr]
    simp only [Category.assoc]

end S_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_affine_smooth_local_lift_opens_pullback (solution)
