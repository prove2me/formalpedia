-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.Iso.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/33e5ce73-631b-558b-9f35-047368696e7c

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace BenchR_ED9

universe u

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def pbCompObj {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  ((pullbackComp f g).symm).app M

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def transportIso {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (ε : X ⟶ Y) (h : ε ≫ b = a)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N) :
    (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N :=
  (pullbackCongr h.symm).app M ≪≫ ((pullbackComp ε b).symm).app M ≪≫ (Scheme.Modules.pullback ε).mapIso φ ≪≫
    (pullbackComp ε b).app N ≪≫ (pullbackCongr h).app N

theorem mul_fst_congr' {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {x₁ y₁ : SchemeHomOver t₁ f} {x₂ y₂ : SchemeHomOver t₂ f} (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  rw [Subtype.ext hx, Subtype.ext hy]

end BenchR_ED9

open BenchR_ED9 in
theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.Iso u₁ u₂)
    (h₁ : PolarisedAbelianScheme.IsPullback φ u₁ v₁) (h₂ : PolarisedAbelianScheme.IsPullback φ u₂ v₂) :
    PolarisedAbelianScheme.Iso v₁ v₂ := by
  obtain ⟨e, he, hmul, hP, hpol⟩ := h
  obtain ⟨g₁, hg₁, hmul₁, hP₁, ⟨φ₁⟩⟩ := h₁
  obtain ⟨g₂, hg₂, hmul₂, hP₂, ⟨φ₂⟩⟩ := h₂
  have he' : e.inv ≫ u₁.f = u₂.f := by rw [Iso.inv_comp_eq, he]

  have w₁₂ : (g₁ ≫ e.hom) ≫ u₂.f = v₁.f ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, he, hg₁.w]
  have w₂₁ : (g₂ ≫ e.inv) ≫ u₁.f = v₂.f ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [Category.assoc, he', hg₂.w]
  let a : v₁.A ⟶ v₂.A := hg₂.lift (g₁ ≫ e.hom) v₁.f w₁₂
  let b : v₂.A ⟶ v₁.A := hg₁.lift (g₂ ≫ e.inv) v₂.f w₂₁
  have ha₁ : a ≫ g₂ = g₁ ≫ e.hom := hg₂.lift_fst _ _ _
  have ha₂ : a ≫ v₂.f = v₁.f := hg₂.lift_snd _ _ _
  have hb₁ : b ≫ g₁ = g₂ ≫ e.inv := hg₁.lift_fst _ _ _
  have hb₂ : b ≫ v₁.f = v₂.f := hg₁.lift_snd _ _ _
  have hab : a ≫ b = 𝟙 _ := by
    apply hg₁.hom_ext
    · rw [Category.assoc, hb₁, ← Category.assoc, ha₁]; simp
    · rw [Category.assoc, hb₂, ha₂]; simp
  have hba : b ≫ a = 𝟙 _ := by
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hb₁]; simp
    · rw [Category.assoc, ha₂, hb₂]; simp
  let E : v₁.A ≅ v₂.A := ⟨a, b, hab, hba⟩
  refine ⟨E, ha₂, ?_, ?_, ?_⟩
  · intro T t x y
    show (v₁.L.mul t x y).1 ≫ a = _
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hmul₁, hmul, hmul₂]
      exact mul_fst_congr' _ rfl (by simp [E, ha₁]) (by simp [E, ha₁])
    · rw [Category.assoc, ha₂, (v₁.L.mul t x y).2, (v₂.L.mul t _ _).2]
  · intro i
    show (v₁.P i).1 ≫ a = (v₂.P i).1
    apply hg₂.hom_ext
    · rw [Category.assoc, ha₁, ← Category.assoc, hP₁, Category.assoc, hP, hP₂]
    · rw [Category.assoc, ha₂, (v₁.P i).2, (v₂.P i).2]
  · intro s'
    obtain ⟨U, hsU, ⟨φU⟩⟩ := hpol ((Spec.map (CommRingCat.ofHom φ)).base s')
    refine ⟨Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U, hsU, ?_⟩
    set V' := v₁.f ⁻¹ᵁ (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) with hV'
    have hle : V' ≤ g₁ ⁻¹ᵁ (u₁.f ⁻¹ᵁ U) := by
      rw [hV', ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hg₁.w]
    let ε := g₁.resLE (u₁.f ⁻¹ᵁ U) V' hle
    have hε : ε ≫ (u₁.f ⁻¹ᵁ U).ι = V'.ι ≫ g₁ := Scheme.Hom.resLE_comp_ι _ _
    show Nonempty ((Scheme.Modules.pullback V'.ι).obj ((Scheme.Modules.pullback a).obj v₂.pol) ≅
      (Scheme.Modules.pullback V'.ι).obj v₁.pol)
    exact ⟨(Scheme.Modules.pullback V'.ι).mapIso
        ((Scheme.Modules.pullback a).mapIso φ₂.symm ≪≫ (pbCompObj a g₂ u₂.pol).symm ≪≫
          (Scheme.Modules.pullbackCongr ha₁).app u₂.pol ≪≫ pbCompObj g₁ e.hom u₂.pol) ≪≫
      (pbCompObj V'.ι g₁ _).symm ≪≫ transportIso _ _ ε hε φU ≪≫ pbCompObj V'.ι g₁ _ ≪≫
      (Scheme.Modules.pullback V'.ι).mapIso φ₁⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_baseChange (solution)
