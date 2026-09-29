-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7e4bbc30-9d20-5440-940c-a5281e41c792

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback_1

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
    {X : PolarisedAbelianScheme 2 d m S} {X₁ X₂ : PolarisedAbelianScheme 2 d m S'}
    {t : QMStructure Λ star β X} {t₁ : QMStructure Λ star β X₁} {t₂ : QMStructure Λ star β X₂}
    (h₁ : QMStructure.IsPullback φ t t₁) (h₂ : QMStructure.IsPullback φ t t₂) :
    QMStructure.Iso t₁ t₂ := by
  obtain ⟨gA, hg, hmul, hP, ⟨epol⟩, hact, hQ⟩ := h₁
  obtain ⟨gA', hg', hmul', hP', ⟨epol'⟩, hact', hQ'⟩ := h₂
  let e : X₁.A ≅ X₂.A := hg.isoIsPullback _ _ hg'
  have he₁ : e.hom ≫ gA' = gA := hg.isoIsPullback_hom_fst _ _ hg'
  have he₂ : e.hom ≫ X₂.f = X₁.f := hg.isoIsPullback_hom_snd _ _ hg'
  refine ⟨e, he₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro T t' x y
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hmul t' x y, hmul']
      congr 2 <;> exact Subtype.ext (by simp only [Category.assoc, he₁])
    · rw [Category.assoc, he₂, (X₁.L.mul t' x y).2]
      exact ((X₂.L.mul t' _ _).2).symm
  · intro i
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hP i, hP' i]
    · rw [Category.assoc, he₂, (X₁.P i).2, (X₂.P i).2]
  · intro s
    refine ⟨⊤, TopologicalSpace.Opens.mem_top s, ?_⟩
    have E : (Scheme.Modules.pullback e.hom).obj X₂.pol ≅ X₁.pol :=
      (Scheme.Modules.pullback e.hom).mapIso epol'.symm ≪≫ (Scheme.Modules.pullbackComp e.hom gA').app X.pol ≪≫
        (Scheme.Modules.pullbackCongr he₁).app X.pol ≪≫ epol
    exact ⟨(Scheme.Modules.pullback (X₁.f ⁻¹ᵁ ⊤).ι).mapIso E⟩
  · intro x
    apply hg'.hom_ext
    · rw [Category.assoc, he₁, hact x, Category.assoc, hact' x, ← Category.assoc, he₁]
    · rw [Category.assoc, he₂, t₁.act_over x, Category.assoc, t₂.act_over x, he₂]
  · apply hg'.hom_ext
    · rw [Category.assoc, he₁, hQ, hQ']
    · rw [Category.assoc, he₂, t₁.P.2, t₂.P.2]

end S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback_1
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback_1 (solution)
