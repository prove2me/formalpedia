-- Prove2me | solution 1 for AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6b6aedd3-41f2-5ded-a41a-8d7f1f0a167e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X X' : Scheme.{u}} (pr : X' ⟶ X) (U : X.Opens) {Q Q' : Type u} [CommRing Q] [CommRing Q']
    (f : (↑U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q))
    (hWU : pr ⁻¹ᵁ (U.ι ''ᵁ ⊤) = pr ⁻¹ᵁ U)
    (g : (↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}) ⟶ Spec (CommRingCat.of Q')) (ψ : Q →+* Q')
    (hfac : g ≫ Spec.map (CommRingCat.ofHom ψ) = (X'.isoOfEq hWU).hom ≫ (pr ∣_ U) ≫ f)
    (t : Q) (x' : ↥X') (hx' : x' ∈ pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) :
    ((pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)).ι.stalkMap ⟨x', hx'⟩).hom
        ((X'.presheaf.germ (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) x' hx').hom
          ((pr.app (U.ι ''ᵁ ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))))) =
      ((↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}).presheaf.germ ⊤ ⟨x', hx'⟩ trivial).hom
        ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t))) := by
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t) =
      (Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) := by
    change (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of Q')).inv).hom t = _
    rw [Scheme.ΓSpecIso_inv_naturality]; rfl
  have hR : (g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t)) =
      ((X'.isoOfEq hWU).hom ≫ (pr ∣_ U) ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) := by
    rw [hnat, ← hfac]; rfl
  have hL : (pr.app (U.ι ''ᵁ ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))) =
      (pr.app (U.ι ''ᵁ ⊤)).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t)) := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]; rfl
  rw [hR, hL]
  erw [Scheme.Hom.germ_stalkMap_apply]
  refine TopCat.Presheaf.germ_ext _ ((pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)).ι ⁻¹ᵁ (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤))) hx' (𝟙 _) (homOfLE le_top) ?_

  set a := (pr.app (U.ι ''ᵁ ⊤)).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t)) with ha
  have hRHS : ((X'.isoOfEq hWU).hom ≫ (pr ∣_ U) ≫ f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t) =
      ((X'.isoOfEq hWU).hom.appTop).hom ((X'.presheaf.map (eqToHom (image_morphismRestrict_preimage pr U ⊤)).op).hom a) := by
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, morphismRestrict_appTop, ha]; rfl
  rw [hRHS]
  simp only [Scheme.isoOfEq_hom, Scheme.homOfLE_appTop, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
  rw [ha]

  have key : ∀ (b : Γ(X', pr ⁻¹ᵁ (U.ι ''ᵁ ⊤))) {B C D : (TopologicalSpace.Opens ↥X')ᵒᵖ}
      (m : Opposite.op (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) ⟶ D) (e₁ : Opposite.op (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) ⟶ B) (h₁ : B ⟶ C) (k₁ : C ⟶ D),
      (X'.presheaf.map m).hom b = (X'.presheaf.map k₁).hom ((X'.presheaf.map h₁).hom ((X'.presheaf.map e₁).hom b)) := by
    intro b B C D m e₁ h₁ k₁
    have hm : m = e₁ ≫ h₁ ≫ k₁ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, hm]
  first
    | exact key _ _ _ _ _
    | (erw [← CommRingCat.comp_apply, ← X'.presheaf.map_comp]; exact key _ _ _ _ _)

end S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
end P2MW
export P2MW.S_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp (solution)
