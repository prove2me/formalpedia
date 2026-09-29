-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/cfc707f6-7b80-5a53-bbea-a38f8e61bc58

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

namespace C7QM

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def pbCompObj {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  ((pullbackComp f g).symm).app M

theorem mul_fst_congr' {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {x₁ y₁ : SchemeHomOver t₁ f} {x₂ y₂ : SchemeHomOver t₂ f} (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  rw [Subtype.ext hx, Subtype.ext hy]

theorem specMap_ofHom_comp {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'') :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def transportIso {X Y Z : Scheme.{0}} (a : X ⟶ Z) (b : Y ⟶ Z) (ε : X ⟶ Y) (h : ε ≫ b = a)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N) :
    (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N :=
  (pullbackCongr h.symm).app M ≪≫ ((pullbackComp ε b).symm).app M ≪≫ (Scheme.Modules.pullback ε).mapIso φ ≪≫
    (pullbackComp ε b).app N ≪≫ (pullbackCongr h).app N

end C7QM

open C7QM in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X₁ X₂ : PolarisedAbelianScheme 2 d m S} {X₁' X₂' : PolarisedAbelianScheme 2 d m S'}
    {t₁ : QMStructure Λ star β X₁} {t₂ : QMStructure Λ star β X₂}
    {t₁' : QMStructure Λ star β X₁'} {t₂' : QMStructure Λ star β X₂'}
    (h : QMStructure.Iso t₁ t₂) (h₁ : QMStructure.IsPullback φ t₁ t₁') (h₂ : QMStructure.IsPullback φ t₂ t₂') :
    QMStructure.Iso t₁' t₂' := by
  obtain ⟨e, he, hmul, hP, hpol, hacte, hQe⟩ := h
  obtain ⟨g₁, hg₁, hmul₁, hP₁, ⟨φ₁⟩, hact₁, hQ₁⟩ := h₁
  obtain ⟨g₂, hg₂, hmul₂, hP₂, ⟨φ₂⟩, hact₂, hQ₂⟩ := h₂
  have he' : e.inv ≫ X₁.f = X₂.f := by rw [Iso.inv_comp_eq, he]
  have w₁₂ : (g₁ ≫ e.hom) ≫ X₂.f = X₁'.f ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, he, hg₁.w]
  have w₂₁ : (g₂ ≫ e.inv) ≫ X₁.f = X₂'.f ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, he', hg₂.w]
  let a' : X₁'.A ⟶ X₂'.A := hg₂.lift (g₁ ≫ e.hom) X₁'.f w₁₂
  let b' : X₂'.A ⟶ X₁'.A := hg₁.lift (g₂ ≫ e.inv) X₂'.f w₂₁
  have ha₁ : a' ≫ g₂ = g₁ ≫ e.hom := hg₂.lift_fst _ _ _
  have ha₂ : a' ≫ X₂'.f = X₁'.f := hg₂.lift_snd _ _ _
  have hb₁ : b' ≫ g₁ = g₂ ≫ e.inv := hg₁.lift_fst _ _ _
  have hb₂ : b' ≫ X₁'.f = X₂'.f := hg₁.lift_snd _ _ _
  have hab : a' ≫ b' = 𝟙 _ := by
    apply hg₁.hom_ext
    · rw [Category.assoc, hb₁, ← Category.assoc, ha₁]; simp
    · rw [Category.assoc, hb₂, ha₂]; simp
  have hba : b' ≫ a' = 𝟙 _ := by
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hb₁]; simp
    · rw [Category.assoc, ha₂, hb₂]; simp
  let E : X₁'.A ≅ X₂'.A := ⟨a', b', hab, hba⟩
  refine ⟨E, ha₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t x y
    show (X₁'.L.mul t x y).1 ≫ a' = _
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hmul₁, hmul, hmul₂]
      exact mul_fst_congr' _ rfl (by simp [E, ha₁]) (by simp [E, ha₁])
    · rw [Category.assoc, ha₂, (X₁'.L.mul t x y).2, (X₂'.L.mul t _ _).2]
  · intro i
    show (X₁'.P i).1 ≫ a' = (X₂'.P i).1
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hP₁, Category.assoc, hP, hP₂]
    · rw [Category.assoc, ha₂, (X₁'.P i).2, (X₂'.P i).2]
  · intro s'
    obtain ⟨U, hsU, ⟨φU⟩⟩ := hpol ((Spec.map (CommRingCat.ofHom φ)).base s')
    refine ⟨Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U, hsU, ?_⟩
    set V' := X₁'.f ⁻¹ᵁ (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) with hV'
    have hle : V' ≤ g₁ ⁻¹ᵁ (X₁.f ⁻¹ᵁ U) := by
      rw [hV', ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg₁.w]
    let ε := g₁.resLE (X₁.f ⁻¹ᵁ U) V' hle
    have hε : ε ≫ (X₁.f ⁻¹ᵁ U).ι = V'.ι ≫ g₁ := Scheme.Hom.resLE_comp_ι _ _
    show Nonempty ((Scheme.Modules.pullback V'.ι).obj ((Scheme.Modules.pullback a').obj X₂'.pol) ≅
      (Scheme.Modules.pullback V'.ι).obj X₁'.pol)
    exact ⟨(Scheme.Modules.pullback V'.ι).mapIso
        ((Scheme.Modules.pullback a').mapIso φ₂.symm ≪≫ (pbCompObj a' g₂ X₂.pol).symm ≪≫
          (Scheme.Modules.pullbackCongr ha₁).app X₂.pol ≪≫ pbCompObj g₁ e.hom X₂.pol) ≪≫
      (pbCompObj V'.ι g₁ _).symm ≪≫ transportIso _ _ ε hε φU ≪≫ pbCompObj V'.ι g₁ _ ≪≫
      (Scheme.Modules.pullback V'.ι).mapIso φ₁⟩
  · intro x
    show t₁'.act x ≫ a' = a' ≫ t₂'.act x
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hact₁ x, Category.assoc, hacte x, ← Category.assoc,
        ← ha₁, Category.assoc, Category.assoc, hact₂ x]
    · rw [Category.assoc, ha₂, t₁'.act_over x, Category.assoc, t₂'.act_over x, ha₂]
  · show t₁'.P.1 ≫ a' = t₂'.P.1
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hQ₁, Category.assoc, hQe, hQ₂]
    · rw [Category.assoc, ha₂, t₁'.P.2, t₂'.P.2]

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback (solution)
