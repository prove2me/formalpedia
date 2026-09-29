-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ce9e288d-b705-5e3d-9f64-16bf2cf8ab44

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso.AlgebraicGeometry Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.toPresheaf Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Scheme.Hom.image_top_eq_opensRange Spec Spec.map Scheme Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.comp_appLE Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Modules.map_smul Scheme.Hom.appLE_appIso_inv Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.geomFibreH0Finrank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.toPresheaf Modules.Hom.app_smul Modules.pullback Hom Γ Modules.Hom Hom.image_top_eq_opensRange Modules.restrictFunctorIsoPullback Hom.comp_appLE Hom.opensRange_of_isIso Modules.pullbackCongr Modules Hom.appLE_map Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE_appIso_inv Modules.pullbackComp ΓSpecIso Modules.geomFibreH0Finrank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf Hom.app_smul pseudofunctor pullback presheaf Hom restrictFunctorIsoPullback pullbackCongr restrict map_smul pullbackComp geomFibreH0Finrank"
namespace GeomFibreH0Aux
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {k : Type u} [Field k]

noncomputable def toΓ {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k)) : CommRingCat.of k ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ le_top

noncomputable def h0 {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k)) (N : X.Modules) : ℕ :=
  letI : Algebra k Γ(X, ⊤) := (toΓ g).hom.toAlgebra
  letI : Module k Γ(N, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
  Module.finrank k Γ(N, ⊤)

theorem geomFibreH0Finrank_eq_h0 {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (M : A.Modules) (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f M k sk =
      h0 (pullback.snd f (Spec.map (CommRingCat.ofHom sk)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M) :=
  rfl

theorem toΓ_comp_map_eq {X X₀ : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k)) (e : X₀ ≅ X)
    (htop : e.hom ''ᵁ ⊤ = ⊤) :
    toΓ g ≫ X.presheaf.map (eqToHom htop).op = toΓ (e.hom ≫ g) ≫ (e.hom.appIso ⊤).inv := by
  simp only [toΓ, Category.assoc, Scheme.Hom.comp_appLE, Scheme.Hom.appLE_appIso_inv, Scheme.Hom.appLE_map]
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

theorem h0_eq_of_iso {X X₀ : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k)) (g₀ : X₀ ⟶ Spec (CommRingCat.of k))
    (e : X₀ ≅ X) (he : e.hom ≫ g = g₀) (N : X.Modules) (N₀ : X₀.Modules)
    (ι : (Scheme.Modules.pullback e.hom).obj N ≅ N₀) : h0 g N = h0 g₀ N₀ := by
  subst he
  letI iX : Algebra k Γ(X, ⊤) := (toΓ g).hom.toAlgebra
  letI mX : Module k Γ(N, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
  letI iX₀ : Algebra k Γ(X₀, ⊤) := (toΓ (e.hom ≫ g)).hom.toAlgebra
  letI mX₀ : Module k Γ(N₀, ⊤) := Module.compHom _ (algebraMap k Γ(X₀, ⊤))
  show Module.finrank k Γ(N, ⊤) = Module.finrank k Γ(N₀, ⊤)
  have htop : e.hom ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]

  let a1 : Γ(N, ⊤) ≅ Γ(N, e.hom ''ᵁ ⊤) := N.presheaf.mapIso (eqToIso htop).op

  let a2 : Γ(N.restrict e.hom, ⊤) ≅ Γ(N₀, ⊤) :=
    ((Scheme.Modules.toPresheaf X₀).mapIso ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app N ≪≫ ι)).app (op ⊤)
  let T : Γ(N, ⊤) ≃+ Γ(N₀, ⊤) := (a1 ≪≫ a2).addCommGroupIsoToAddEquiv

  have key : ∀ c : k, X.presheaf.map (eqToHom htop).op (toΓ g c) = (e.hom.appIso ⊤).inv (toΓ (e.hom ≫ g) c) := by
    intro c
    have := congrArg (fun φ => (φ : CommRingCat.of k ⟶ Γ(X, e.hom ''ᵁ ⊤)) c) (toΓ_comp_map_eq g e htop)
    simpa using this
  have hT : ∀ (c : k) (v : Γ(N, ⊤)), T (c • v) = c • T v := by
    intro c v

    change a2.hom (a1.hom ((toΓ g c) • v)) = (toΓ (e.hom ≫ g) c) • a2.hom (a1.hom v)
    have h1 : a1.hom ((toΓ g c) • v) = X.presheaf.map (eqToHom htop).op (toΓ g c) • a1.hom v :=
      Scheme.Modules.map_smul N (eqToHom htop) _ _
    rw [h1, key c]

    exact Scheme.Modules.Hom.app_smul
      (((Scheme.Modules.restrictFunctorIsoPullback e.hom).app N ≪≫ ι).hom) (toΓ (e.hom ≫ g) c) (a1.hom v)
  let T' : Γ(N, ⊤) ≃ₗ[k] Γ(N₀, ⊤) :=
    { toFun := T, map_add' := T.map_add, map_smul' := hT, invFun := T.symm,
      left_inv := T.left_inv, right_inv := T.right_inv }
  exact T'.finrank_eq

end AlgebraicGeometry.Scheme.Modules.GeomFibreH0Aux

open AlgebraicGeometry.Scheme.Modules.GeomFibreH0Aux in
theorem solution
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (φ : S →+* S₀)
    {A A₀ : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀))
    (t : A₀ ⟶ A) (ht : IsPullback t f₀ f (Spec.map (CommRingCat.ofHom φ)))
    (M : A.Modules) (M₀ : A₀.Modules) (hiso : Nonempty ((Scheme.Modules.pullback t).obj M ≅ M₀))
    (k : Type u) [Field k] (sk₀ : S₀ →+* k) :
    Scheme.Modules.geomFibreH0Finrank f M k (sk₀.comp φ) = Scheme.Modules.geomFibreH0Finrank f₀ M₀ k sk₀ := by
  obtain ⟨ι⟩ := hiso
  have hσ : Spec.map (CommRingCat.ofHom (sk₀.comp φ)) =
      Spec.map (CommRingCat.ofHom sk₀) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hX₀ : IsPullback (pullback.fst f₀ (Spec.map (CommRingCat.ofHom sk₀)) ≫ t)
      (pullback.snd f₀ (Spec.map (CommRingCat.ofHom sk₀))) f
      (Spec.map (CommRingCat.ofHom sk₀) ≫ Spec.map (CommRingCat.ofHom φ)) :=
    (IsPullback.of_hasPullback f₀ (Spec.map (CommRingCat.ofHom sk₀))).paste_horiz ht
  have hX : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (sk₀.comp φ))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (sk₀.comp φ)))) f
      (Spec.map (CommRingCat.ofHom sk₀) ≫ Spec.map (CommRingCat.ofHom φ)) := by
    rw [← hσ]
    exact IsPullback.of_hasPullback _ _
  let e := hX₀.isoIsPullback _ _ hX
  have he₁ : e.hom ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (sk₀.comp φ))) =
      pullback.fst f₀ (Spec.map (CommRingCat.ofHom sk₀)) ≫ t :=
    hX₀.isoIsPullback_hom_fst _ _ hX
  have he₂ : e.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (sk₀.comp φ))) =
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom sk₀)) :=
    hX₀.isoIsPullback_hom_snd _ _ hX

  let ιM : (Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (sk₀.comp φ))))).obj M) ≅
      (Scheme.Modules.pullback (pullback.fst f₀ (Spec.map (CommRingCat.ofHom sk₀)))).obj M₀ :=
    (Scheme.Modules.pullbackComp e.hom _).app M ≪≫
      (Scheme.Modules.pullbackCongr he₁).app M ≪≫
        ((Scheme.Modules.pullbackComp _ t).app M).symm ≪≫
          (Scheme.Modules.pullback _).mapIso ι
  rw [geomFibreH0Finrank_eq_h0, geomFibreH0Finrank_eq_h0]
  exact h0_eq_of_iso _ _ e he₂ _ _ ιM

end S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq_of_isPullback_of_iso (solution)
