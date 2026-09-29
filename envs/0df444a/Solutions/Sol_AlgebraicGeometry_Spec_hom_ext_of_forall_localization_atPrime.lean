-- Prove2me | solution 1 for AlgebraicGeometry.Spec_hom_ext_of_forall_localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c9ab24ed-1737-58ab-a504-51b23167bd58

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace LocGlob29

p2m_open "Opposite TopologicalSpace AlgebraicGeometry.Scheme IsLocalRing"

theorem tail_eq_id (R : CommRingCat.{u}) [IsLocalRing R] (V : (Spec R).Opens) (hV : V = ⊤) :
    (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      ((Spec R).presheaf.mapIso (eqToIso hV.symm).op ≪≫ ΓSpecIso R).hom = 𝟙 _ := by
  subst hV
  have h1 : (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : (Spec R).Opens)) := rfl
  rw [h1, CategoryTheory.Functor.map_id, Category.id_comp]
  simp

theorem app_germ_eq {X Z : Scheme.{u}} (f g : X ⟶ Z) (x : X)
    (h : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g)
    (W : Z.Opens) (hx : f.base x ∈ W) (hx' : g.base x ∈ W) :
    f.app W ≫ X.presheaf.germ (f ⁻¹ᵁ W) x hx = g.app W ≫ X.presheaf.germ (g ⁻¹ᵁ W) x hx' := by
  have key : ∀ (F₁ F₂ : Spec (X.presheaf.stalk x) ⟶ Z), F₁ = F₂ →
      ∀ (h₁ : F₁.base (closedPoint (X.presheaf.stalk x)) ∈ W) (h₂ : F₂.base (closedPoint (X.presheaf.stalk x)) ∈ W),
      Z.presheaf.germ W _ h₁ ≫ Scheme.stalkClosedPointTo F₁ = Z.presheaf.germ W _ h₂ ≫ Scheme.stalkClosedPointTo F₂ := by
    rintro F₁ F₂ rfl h₁ h₂; rfl

  suffices H : ∀ (y : X), y = x → ∀ (h1 : f.base y ∈ W) (h2 : g.base y ∈ W),
      f.app W ≫ X.presheaf.germ (f ⁻¹ᵁ W) y h1 = g.app W ≫ X.presheaf.germ (g ⁻¹ᵁ W) y h2 by
    exact H x rfl hx hx'
  rintro y hy h1 h2
  have hcp : (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x := Scheme.fromSpecStalk_closedPoint

  obtain rfl : y = (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) := hy.trans hcp.symm
  have e := key _ _ h h1 h2
  rw [Scheme.stalkClosedPointTo_comp, Scheme.stalkClosedPointTo_comp] at e
  change Z.presheaf.germ W (f.base _) h1 ≫ f.stalkMap _ ≫ Scheme.stalkClosedPointTo (X.fromSpecStalk x) =
    Z.presheaf.germ W (g.base _) h2 ≫ g.stalkMap _ ≫ Scheme.stalkClosedPointTo (X.fromSpecStalk x) at e
  rw [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.germ_stalkMap_assoc] at e
  rw [Scheme.stalkClosedPointTo_fromSpecStalk] at e
  simp only [← Category.assoc] at e
  simpa only [Category.assoc] using (cancel_mono _).mp e

theorem hom_ext_of_fromSpecStalk {X Z : Scheme.{u}} (f g : X ⟶ Z)
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have hpt : ∀ x : X, f.base x = g.base x := by
    intro x
    have e := congrArg (fun F : Spec (X.presheaf.stalk x) ⟶ Z => F.base (closedPoint (X.presheaf.stalk x))) (h x)
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at e
    exact e
  refine Scheme.hom_ext_of_forall f g fun x => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  have hxW' : g.base x ∈ W := hpt x ▸ hxW
  refine ⟨f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W, ⟨hxW, hxW'⟩, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f (inf_le_left : f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W ≤ f ⁻¹ᵁ W),
    ← Scheme.Hom.resLE_comp_ι g (inf_le_right : f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W ≤ g ⁻¹ᵁ W)]
  congr 1
  haveI : IsAffine W := hW
  apply ext_of_isAffine
  simp only [Scheme.Hom.resLE_app_top]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  apply TopCat.Presheaf.section_ext X.sheaf (f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W)
  intro y hy
  have e := app_germ_eq f g y (h y) W hy.1 hy.2
  have e1 : X.presheaf.germ (f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W) y hy (f.appLE W (f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W) inf_le_left s) =
      (f.app W ≫ X.presheaf.germ (f ⁻¹ᵁ W) y hy.1) s := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) y hy _
  have e2 : X.presheaf.germ (f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W) y hy (g.appLE W (f ⁻¹ᵁ W ⊓ g ⁻¹ᵁ W) inf_le_right s) =
      (g.app W ≫ X.presheaf.germ (g ⁻¹ᵁ W) y hy.2) s := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) y hy _
  show X.presheaf.germ _ y hy (f.appLE W _ inf_le_left s) = X.presheaf.germ _ y hy (g.appLE W _ inf_le_right s)
  rw [e1, e2, e]

theorem fromSpecStalk_eq_comp (B : Type u) [CommRing B] (p : PrimeSpectrum B) :
    ∃ e : Spec ((Spec (CommRingCat.of B)).presheaf.stalk p) ⟶ Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)),
      (Spec (CommRingCat.of B)).fromSpecStalk p =
        e ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) := by
  let S := (Spec.structureSheaf B).presheaf.stalk p
  let ε : Localization.AtPrime p.asIdeal ≃ₐ[B] S :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) S
  refine ⟨Spec.map (CommRingCat.ofHom ε.toRingHom), ?_⟩
  rw [← Spec.map_comp, Spec.fromSpecStalk_eq']
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  show StructureSheaf.toStalk B p r = ε (algebraMap B (Localization.AtPrime p.asIdeal) r)
  rw [AlgEquiv.commutes, StructureSheaf.stalkAlgebra_map]

end LocGlob29

theorem solution
    {B : Type u} [CommRing B] {Z : Scheme.{u}} (f g : Spec (CommRingCat.of B) ⟶ Z)
    (h : ∀ p : PrimeSpectrum B,
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ g) :
    f = g := by
  refine LocGlob29.hom_ext_of_fromSpecStalk f g fun p => ?_
  obtain ⟨e, he⟩ := LocGlob29.fromSpecStalk_eq_comp B p
  rw [he, Category.assoc, Category.assoc, h p]

end S_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime
end P2MW
export P2MW.S_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime (solution)
