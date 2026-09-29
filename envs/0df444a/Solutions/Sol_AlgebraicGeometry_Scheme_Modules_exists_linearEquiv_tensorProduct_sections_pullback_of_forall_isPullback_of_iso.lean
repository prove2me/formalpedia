-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/be0adb22-d91d-5b2d-843b-2e40d72967e5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.comp_appTop Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Modules.conjugateEquiv_pullbackComp_inv Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_app"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom ΓSpecIso_inv_naturality Modules.Hom.id_app Modules.Hom.app Hom.comp_appTop Hom.comp_app Modules Opens Hom.app_eq_appLE Modules.conjugateEquiv_pullbackComp_inv Modules.pullbackComp ΓSpecIso Modules.pullbackLocalSection Modules.pullbackLocalSection_app"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforwardComp pullback Hom.comp_app Hom pushforward_map_app Hom.id_app Hom.app pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv map_smul pullbackComp pullbackLocalSection pullbackLocalSection_def pullbackLocalSection_smul pullbackLocalSection_app"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pullbackComp_inv_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) =
      pullbackLocalSection f (pullbackLocalSection g m) := by
  have h1 := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h1
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k U m) h1
  dsimp only at h2
  erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2

  exact h2.symm

theorem pullbackComp_hom_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (pullbackLocalSection f (pullbackLocalSection g m)) =
      pullbackLocalSection (f ≫ g) m := by
  rw [← pullbackComp_inv_app_app_pullbackLocalSection]
  change (((Scheme.Modules.pullbackComp f g).inv.app M) ≫ ((Scheme.Modules.pullbackComp f g).hom.app M)).app
    ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) = _
  rw [Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {S₀ : Type u} [CommRing S₀] {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)) (𝓛₀ : A₀.Modules)
    (hbc₀ : ∀ (B : Type u) [CommRing B] (ψ : S₀ →+* B)
      (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ A₀),
      IsPullback g f' f₀ (Spec.map (CommRingCat.ofHom ψ)) →
      letI : Module S₀ Γ(𝓛₀, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S₀)).inv ≫ f₀.appTop).hom
      letI : Module B Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S₀ B := ψ.toAlgebra
      ∃ e : B ⊗[S₀] Γ(𝓛₀, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj 𝓛₀, g ⁻¹ᵁ ⊤),
        ∀ (b : B) (m : Γ(𝓛₀, ⊤)), e (b ⊗ₜ[S₀] m) = b • Scheme.Modules.pullbackLocalSection g m)
    {S : Type u} [CommRing S] (ψ₀ : S₀ →+* S) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (g₀ : A ⟶ A₀)
    (hg₀ : IsPullback g₀ f f₀ (Spec.map (CommRingCat.ofHom ψ₀)))
    (𝓛 : A.Modules) (e₀ : (Scheme.Modules.pullback g₀).obj 𝓛₀ ≅ 𝓛)
    (S' : Type u) [CommRing S'] (φ : S →+* S')
    (A' : Scheme.{u}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
    (hg : IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
    letI : Module S' Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra S S' := φ.toAlgebra
    ∃ e : S' ⊗[S] Γ(𝓛, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤),
      ∀ (b : S') (m : Γ(𝓛, ⊤)), e (b ⊗ₜ[S] m) = b • Scheme.Modules.pullbackLocalSection gA m := by
  letI algS : Algebra S₀ S := ψ₀.toAlgebra
  letI algS' : Algebra S S' := φ.toAlgebra
  letI algS₀S' : Algebra S₀ S' := (φ.comp ψ₀).toAlgebra
  haveI hst : IsScalarTower S₀ S S' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI mΓ₀ : Module S₀ Γ(𝓛₀, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S₀)).inv ≫ f₀.appTop).hom
  letI mΓ : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
  letI m1 : Module S Γ((Scheme.Modules.pullback g₀).obj 𝓛₀, g₀ ⁻¹ᵁ ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ (g₀ ⁻¹ᵁ ⊤) le_top).hom
  letI m2 : Module S' Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
  letI m3 : Module S' Γ((Scheme.Modules.pullback (gA ≫ g₀)).obj 𝓛₀, (gA ≫ g₀) ⁻¹ᵁ ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ ((gA ≫ g₀) ⁻¹ᵁ ⊤) le_top).hom

  obtain ⟨eS, heS⟩ := hbc₀ S ψ₀ A f g₀ hg₀

  have hgg : IsPullback (gA ≫ g₀) f' f₀ (Spec.map (CommRingCat.ofHom (φ.comp ψ₀))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact IsPullback.paste_horiz hg hg₀
  obtain ⟨eS', heS'⟩ := hbc₀ S' (φ.comp ψ₀) A' f' (gA ≫ g₀) hgg

  have happLE : f.appLE ⊤ (g₀ ⁻¹ᵁ ⊤) le_top = f.appTop := (Scheme.Hom.app_eq_appLE f).symm

  let α₀ : Γ((Scheme.Modules.pullback g₀).obj 𝓛₀, g₀ ⁻¹ᵁ ⊤) →ₗ[S] Γ(𝓛, ⊤) :=
    { toFun := fun y => e₀.hom.app ⊤ y
      map_add' := fun y y' => map_add _ y y'
      map_smul' := fun s y => by
        change e₀.hom.app ⊤
            (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ (g₀ ⁻¹ᵁ ⊤) le_top) s • y) =
          ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop) s • e₀.hom.app ⊤ y
        erw [Scheme.Modules.Hom.app_smul]
        rw [happLE]
        rfl }
  have hα₀ : Function.Bijective α₀ := ConcreteCategory.bijective_of_isIso (e₀.hom.app ⊤)
  let α : S ⊗[S₀] Γ(𝓛₀, ⊤) ≃ₗ[S] Γ(𝓛, ⊤) := eS.trans (LinearEquiv.ofBijective α₀ hα₀)
  have hα : ∀ (s : S) (m : Γ(𝓛₀, ⊤)), α (s ⊗ₜ[S₀] m) =
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop) s • e₀.hom.app ⊤ (pullbackLocalSection g₀ m) := by
    intro s m
    show α₀ (eS (s ⊗ₜ[S₀] m)) = _
    rw [heS, LinearMap.map_smul]
    rfl

  let θ := ((Scheme.Modules.pullbackComp gA g₀).inv.app 𝓛₀).app (gA ⁻¹ᵁ ⊤)
  let η := ((Scheme.Modules.pullback gA).map e₀.hom).app (gA ⁻¹ᵁ ⊤)
  let β₀ : Γ((Scheme.Modules.pullback (gA ≫ g₀)).obj 𝓛₀, (gA ≫ g₀) ⁻¹ᵁ ⊤) →ₗ[S']
      Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
    { toFun := fun y => η (θ y)
      map_add' := fun y y' => by
        show η (θ (y + y')) = η (θ y) + η (θ y')
        erw [map_add, map_add]
      map_smul' := fun b y => by
        change η (θ (((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ ((gA ≫ g₀) ⁻¹ᵁ ⊤) le_top) b • y)) =
          ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top) b • η (θ y)
        erw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
        rfl }
  have hβ₀ : Function.Bijective β₀ := (ConcreteCategory.bijective_of_isIso η).comp (ConcreteCategory.bijective_of_isIso θ)
  let β : S' ⊗[S₀] Γ(𝓛₀, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
    eS'.trans (LinearEquiv.ofBijective β₀ hβ₀)
  have hβ : ∀ (b : S') (m : Γ(𝓛₀, ⊤)), β (b ⊗ₜ[S₀] m) =
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top) b •
        pullbackLocalSection gA (e₀.hom.app ⊤ (pullbackLocalSection g₀ m)) := by
    intro b m
    show β₀ (eS' (b ⊗ₜ[S₀] m)) = _
    rw [heS', LinearMap.map_smul]
    show _ • η (θ (pullbackLocalSection (gA ≫ g₀) m)) = _
    congr 1
    show η (θ (pullbackLocalSection (gA ≫ g₀) m)) = _
    rw [show θ (pullbackLocalSection (gA ≫ g₀) m) = pullbackLocalSection gA (pullbackLocalSection g₀ m) from
      Scheme.Modules.pullbackComp_inv_app_app_pullbackLocalSection gA g₀ 𝓛₀ ⊤ m]
    exact (Scheme.Modules.pullbackLocalSection_app gA e₀.hom (pullbackLocalSection g₀ m)).symm

  have hadd : ∀ u v : Γ(𝓛, ⊤), pullbackLocalSection gA (u + v) = pullbackLocalSection gA u + pullbackLocalSection gA v := by
    intro u v
    rw [pullbackLocalSection_def, pullbackLocalSection_def, pullbackLocalSection_def]
    erw [map_add]
    rfl
  have hzero : pullbackLocalSection gA (0 : Γ(𝓛, ⊤)) = 0 := by
    rw [pullbackLocalSection_def]
    erw [map_zero]
    rfl

  have hring : (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop ≫ gA.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top := by
    have h1 : f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top = f'.appTop := (Scheme.Hom.app_eq_appLE f').symm
    rw [h1, ← Scheme.Hom.comp_appTop, hg.w, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hsc : ∀ (s : S) (w : Γ(𝓛, ⊤)),
      pullbackLocalSection gA (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop) s • w) =
        ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top) (φ s) •
          pullbackLocalSection gA w := by
    intro s w
    rw [pullbackLocalSection_smul]
    congr 1
    exact congrArg (fun k : (CommRingCat.of S) ⟶ Γ(A', gA ⁻¹ᵁ ⊤) => k.hom s) hring

  let E : S' ⊗[S] Γ(𝓛, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤) :=
    ((LinearEquiv.baseChange S S' _ _ α).symm.trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S₀ S S' S' Γ(𝓛₀, ⊤))).trans β
  have hsm : ∀ (b' : S') (z : Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤)),
      b' • z = ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top) b' • z := fun _ _ => rfl
  have key : ∀ (x : S ⊗[S₀] Γ(𝓛₀, ⊤)) (b : S'),
      β (TensorProduct.AlgebraTensorModule.cancelBaseChange S₀ S S' S' Γ(𝓛₀, ⊤) (b ⊗ₜ[S] x)) =
        b • pullbackLocalSection gA (α x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      intro b
      rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, hzero, smul_zero]
    | tmul s m₀ =>
      intro b
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, hβ, hα, hsc, hsm, ← mul_smul, ← map_mul,
        Algebra.smul_def]
      congr 1
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top) (b * φ s)
      rw [mul_comm]
      rfl
    | add x y hx hy =>
      intro b
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add, hadd, smul_add]
  refine ⟨E, fun b m => ?_⟩
  obtain ⟨x, rfl⟩ := α.surjective m
  have hE : E (b ⊗ₜ[S] α x) = β (TensorProduct.AlgebraTensorModule.cancelBaseChange S₀ S S' S' Γ(𝓛₀, ⊤) (b ⊗ₜ[S] x)) := by
    show β (TensorProduct.AlgebraTensorModule.cancelBaseChange S₀ S S' S' Γ(𝓛₀, ⊤)
      ((LinearEquiv.baseChange S S' _ _ α).symm (b ⊗ₜ[S] α x))) = _
    rw [show (LinearEquiv.baseChange S S' _ _ α).symm (b ⊗ₜ[S] α x) = b ⊗ₜ[S] x from by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul]]
  rw [hE]
  exact key x b

end S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_forall_isPullback_of_iso (solution)
