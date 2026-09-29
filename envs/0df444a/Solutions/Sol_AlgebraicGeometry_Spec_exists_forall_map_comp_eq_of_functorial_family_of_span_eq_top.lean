-- Prove2me | solution 1 for AlgebraicGeometry.Spec.exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5d6717d7-4799-5670-8f5a-0466708f7aeb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type} [CommRing S] {Y : Scheme.{0}}

    (adm : ∀ (S' : Type) [CommRing S'], (S →+* S') → Prop)
    (hadm : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (χ : S' →+* S''),
      adm S' ψ → adm S'' (χ.comp ψ))

    (z : ∀ (S' : Type) [CommRing S'] (ψ : S →+* S'), adm S' ψ → (Spec (CommRingCat.of S') ⟶ Y))
    (hz : ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S →+* S') (hψ : adm S' ψ) (χ : S' →+* S'')
      (hχ : adm S'' (χ.comp ψ)), z S'' (χ.comp ψ) hχ = Spec.map (CommRingCat.ofHom χ) ≫ z S' ψ hψ)

    (R : Set S) (hR : Ideal.span R = ⊤)
    (hcov : ∀ r ∈ R, adm (Localization.Away r) (algebraMap S (Localization.Away r))) :
    ∃ q : Spec (CommRingCat.of S) ⟶ Y,
      (∀ (S' : Type) [CommRing S'] (ψ : S →+* S') (hψ : adm S' ψ), Spec.map (CommRingCat.ofHom ψ) ≫ q = z S' ψ hψ) ∧
      ∀ q' : Spec (CommRingCat.of S) ⟶ Y,
        (∀ r (hr : r ∈ R), Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) ≫ q' =
          z (Localization.Away r) (algebraMap S (Localization.Away r)) (hcov r hr)) → q' = q := by
  classical
  have hzcongr : ∀ (S' : Type) [CommRing S'] (ψ₁ ψ₂ : S →+* S') (h : ψ₁ = ψ₂) (h₁ : adm S' ψ₁) (h₂ : adm S' ψ₂),
      z S' ψ₁ h₁ = z S' ψ₂ h₂ := by
    rintro S' _ ψ₁ ψ₂ rfl h₁ h₂; rfl

  have hkey : ∀ (A : CommRingCat.{0}) (S₁ S₂ : Type) [CommRing S₁] [CommRing S₂] (ψ₁ : S →+* S₁) (ψ₂ : S →+* S₂)
      (h₁ : adm S₁ ψ₁) (h₂ : adm S₂ ψ₂) (a : Spec A ⟶ Spec (CommRingCat.of S₁)) (b : Spec A ⟶ Spec (CommRingCat.of S₂)),
      a ≫ Spec.map (CommRingCat.ofHom ψ₁) = b ≫ Spec.map (CommRingCat.ofHom ψ₂) →
      a ≫ z S₁ ψ₁ h₁ = b ≫ z S₂ ψ₂ h₂ := by
    intro A S₁ S₂ _ _ ψ₁ ψ₂ h₁ h₂ a b hab
    obtain ⟨χa, rfl⟩ : ∃ χa : CommRingCat.of S₁ ⟶ A, Spec.map χa = a := ⟨Spec.preimage a, Spec.map_preimage a⟩
    obtain ⟨χb, rfl⟩ : ∃ χb : CommRingCat.of S₂ ⟶ A, Spec.map χb = b := ⟨Spec.preimage b, Spec.map_preimage b⟩
    have hθ : χa.hom.comp ψ₁ = χb.hom.comp ψ₂ := by
      have : Spec.map (CommRingCat.ofHom ψ₁ ≫ χa) = Spec.map (CommRingCat.ofHom ψ₂ ≫ χb) := by
        rw [Spec.map_comp, Spec.map_comp]; exact hab
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have ea := hz S₁ A ψ₁ h₁ χa.hom (hadm S₁ A ψ₁ χa.hom h₁)
    have eb := hz S₂ A ψ₂ h₂ χb.hom (hadm S₂ A ψ₂ χb.hom h₂)
    rw [CommRingCat.ofHom_hom] at ea eb
    rw [← ea, ← eb]
    exact hzcongr A _ _ hθ _ _

  have hcovT : ∀ (T : Type) [CommRing T] (g : S →+* T) (x : ↥(Spec (CommRingCat.of T))),
      ∃ (j : {r : S // r ∈ R}) (y : ↥(Spec (CommRingCat.of (Localization.Away (g j.1))))),
        (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.Away (g j.1))))).base y = x := by
    intro T _ g x
    have hRT : Ideal.span (g '' R) = ⊤ := by rw [← Ideal.map_span, hR, Ideal.map_top]
    have hx : ¬ (g '' R ⊆ (x.asIdeal : Set T)) := by
      intro hsub
      have : (⊤ : Ideal T) ≤ x.asIdeal := hRT ▸ Ideal.span_le.mpr hsub
      exact x.isPrime.ne_top (top_le_iff.mp this)
    obtain ⟨_, ⟨r, hrR, rfl⟩, hrx⟩ := Set.not_subset.mp hx
    have hmem : x ∈ (PrimeSpectrum.basicOpen (g r) : Set (PrimeSpectrum T)) := hrx
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (g r)) (g r)] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨⟨r, hrR⟩, y, hy⟩

  let J := {r : S // r ∈ R}
  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun j => Spec (CommRingCat.of (Localization.Away ((RingHom.id S) j.1))))
      (fun j => Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ((RingHom.id S) j.1)))))
      (hcovT S (RingHom.id S))
  let zloc : ∀ j : J, Spec (CommRingCat.of (Localization.Away ((RingHom.id S) j.1))) ⟶ Y :=
    fun j => z _ (algebraMap S _) (hcov j.1 j.2)
  have hf : ∀ i j : J, pullback.fst (𝒰.f i) (𝒰.f j) ≫ zloc i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ zloc j := by
    intro i j
    refine (pullback (𝒰.f i) (𝒰.f j)).affineCover.hom_ext _ _ fun k => ?_
    have h := hkey _ _ _ _ _ (hcov i.1 i.2) (hcov j.1 j.2)
      ((pullback (𝒰.f i) (𝒰.f j)).affineCover.f k ≫ pullback.fst (𝒰.f i) (𝒰.f j))
      ((pullback (𝒰.f i) (𝒰.f j)).affineCover.f k ≫ pullback.snd (𝒰.f i) (𝒰.f j))
      (by have h__af := (congrArg (fun t => (pullback (𝒰.f i) (𝒰.f j)).affineCover.f k ≫ t) (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))); simp only [Category.assoc] at h__af ⊢; exact h__af)
    simp only [Category.assoc] at h
    exact h
  refine ⟨𝒰.glueMorphisms zloc hf, ?_, ?_⟩
  · intro S' _ ψ hψ
    let 𝒱 : (Spec (CommRingCat.of S')).OpenCover :=
      Scheme.Cover.mkOfCovers J (fun j => Spec (CommRingCat.of (Localization.Away (ψ j.1))))
        (fun j => Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (ψ j.1))))) (hcovT S' ψ)
    refine 𝒱.hom_ext _ _ fun j => ?_
    obtain ⟨r, hrR⟩ := j
    let χ : Localization.Away ((RingHom.id S) r) →+* Localization.Away (ψ r) :=
      IsLocalization.Away.lift ((RingHom.id S) r) (g := (algebraMap S' (Localization.Away (ψ r))).comp ψ)
        (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (ψ r)) (ψ r))
    have hχ : χ.comp (algebraMap S (Localization.Away ((RingHom.id S) r))) = (algebraMap S' (Localization.Away (ψ r))).comp ψ :=
      IsLocalization.Away.lift_comp _ _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (ψ r)))) ≫ Spec.map (CommRingCat.ofHom ψ) =
        Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ((RingHom.id S) r)))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hχ]
    have hq : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ((RingHom.id S) r)))) ≫ 𝒰.glueMorphisms zloc hf =
        zloc ⟨r, hrR⟩ := Scheme.Cover.ι_glueMorphisms 𝒰 zloc hf ⟨r, hrR⟩
    have e2 := hz _ _ (algebraMap S (Localization.Away ((RingHom.id S) r))) (hcov r hrR) χ (hadm _ _ _ χ (hcov r hrR))
    have e3 := hz S' _ ψ hψ (algebraMap S' (Localization.Away (ψ r))) (hadm _ _ _ _ hψ)
    show Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (ψ r)))) ≫ Spec.map (CommRingCat.ofHom ψ) ≫
        𝒰.glueMorphisms zloc hf = Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (ψ r)))) ≫ z S' ψ hψ
    rw [← Category.assoc, e1, Category.assoc, hq]
    show Spec.map (CommRingCat.ofHom χ) ≫ zloc ⟨r, hrR⟩ = _
    rw [← e3]
    show Spec.map (CommRingCat.ofHom χ) ≫ z _ (algebraMap S (Localization.Away ((RingHom.id S) r))) (hcov r hrR) = _
    rw [← e2]
    exact hzcongr _ _ _ hχ _ _
  · intro q' hq'
    exact 𝒰.hom_ext _ _ fun j => by rw [Scheme.Cover.ι_glueMorphisms]; exact hq' j.1 j.2

end S_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_Spec_exists_forall_map_comp_eq_of_functorial_family_of_span_eq_top (solution)
