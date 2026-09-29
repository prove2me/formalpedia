-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/116e9320-807c-5d58-983b-991ac19cb844

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Spec.map Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app IsOpenImmersion Scheme.Modules Scheme.Hom.app_eq_appLE Scheme.Modules.conjugateEquiv_pullbackComp_inv Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.Modules.pullbackLocalSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app restrictFunctor Hom.comp_app Modules Opens Hom.app_eq_appLE Modules.conjugateEquiv_pullbackComp_inv Modules.pullbackComp ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.moduleSectionsOfHom Modules.pullbackLocalSection"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforwardComp pullback presheaf Hom.comp_app Hom pushforward_map_app restrictFunctor Hom.id_app Hom.app restrictFunctorIsoPullback restrictAdjunction pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv map_smul pullbackComp pullbackLocalSection pullbackLocalSection_def pullbackLocalSection_smul"
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

namespace AnySq17

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback.AlgebraicGeometry.Scheme.Modules"

theorem pullbackLocalSection_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : Y.Opens)
    (hU : f ''ᵁ (f ⁻¹ᵁ U) = U) :
    Function.Bijective (fun m : Γ(M, U) => pullbackLocalSection f m) := by
  have key : ∀ m : Γ(M, U), pullbackLocalSection f m =
      (((restrictFunctorIsoPullback f).hom.app M).app (f ⁻¹ᵁ U))
        (M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) := by
    intro m
    have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f) (pullbackPushforwardAdjunction f) M
    have h2 := congrArg (fun k => Scheme.Modules.Hom.app k U m) h
    rw [pullbackLocalSection_def]
    exact h2.symm
  have e1 : Function.Bijective (fun m : Γ(M, U) => M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) := by
    have : (homOfLE (f.image_preimage_le U)).op = (eqToHom hU).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [this, eqToHom_op]
    exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom (congrArg Opposite.op hU.symm))))
  have e2 : Function.Bijective ((((restrictFunctorIsoPullback f).hom.app M).app (f ⁻¹ᵁ U)) :
      Γ((restrictFunctor f).obj M, f ⁻¹ᵁ U) → Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U)) :=
    ConcreteCategory.bijective_of_isIso _
  have : (fun m : Γ(M, U) => pullbackLocalSection f m) =
      (fun y => (((restrictFunctorIsoPullback f).hom.app M).app (f ⁻¹ᵁ U)) y) ∘
        (fun m : Γ(M, U) => M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) := by
    funext m; exact key m
  rw [this]
  exact e2.comp e1

theorem image_preimage_eq_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) :
    f ''ᵁ (f ⁻¹ᵁ U) = U := by
  apply le_antisymm (f.image_preimage_le U)
  intro y hy
  obtain ⟨x, rfl⟩ := f.surjective y
  exact ⟨x, hy, rfl⟩

end AnySq17

open AnySq17 _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (hbc : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (m : Γ(M, ⊤)),
          e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) m)
    (B : Type u) [CommRing B] (φ : R →+* B)
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of B)) (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) :
    letI : Module R Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
    letI : Module B Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
    letI : Algebra R B := φ.toAlgebra
    ∃ e : B ⊗[R] Γ(M, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤),
      ∀ (b : B) (m : Γ(M, ⊤)), e (b ⊗ₜ[R] m) = b • Scheme.Modules.pullbackLocalSection g m := by

  have hρ : ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ ⊤ le_top).hom = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom := by
    have : f.appLE ⊤ ⊤ le_top = f.appTop := (Scheme.Hom.app_eq_appLE f).symm
    rw [this]
  suffices main : ∀ (ρ : R →+* Γ(X, ⊤)), ρ = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom →
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        letI : Module R Γ(M, ⊤) := Module.compHom _ ρ
        letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
          ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
        ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
            Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
              (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
          ∀ (a : A) (m : Γ(M, ⊤)),
            e (a ⊗ₜ[R] m) = a • Scheme.Modules.pullbackLocalSection
              (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) m) →
      letI : Module R Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
      letI : Module B Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra R B := φ.toAlgebra
      ∃ e : B ⊗[R] Γ(M, ⊤) ≃ₗ[B] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤),
        ∀ (b : B) (m : Γ(M, ⊤)), e (b ⊗ₜ[R] m) = b • Scheme.Modules.pullbackLocalSection g m by
    exact main _ hρ hbc
  intro ρ hρ hbc'
  subst hρ
  clear hbc
  letI instRM : Module R Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  letI instRB : Algebra R B := φ.toAlgebra

  have hg' : IsPullback g f' f (Scheme.TwoAffineOpenCover.specMap R B) := hg
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : X' ≅ Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R B),
      κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B) = g ∧
      κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B) = f' :=
    ⟨hg'.isoPullback, hg'.isoPullback_hom_fst, hg'.isoPullback_hom_snd⟩
  subst hκ1 hκ2
  clear hg hg'
  obtain ⟨e₁, he₁⟩ := hbc' B

  letI instB1 := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B))
    ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj M)
    ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤)
  letI instB2 : Module B Γ((Scheme.Modules.pullback (κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj M,
      (κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
        ((κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top).hom

  have hs : ∀ b : B,
      κ.hom.app ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤)
        (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
            ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top) b) =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
          ((κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top) b := by
    intro b
    have hmor : (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
          ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top ≫
        κ.hom.app ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) =
        (κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
          (κ.hom ⁻¹ᵁ ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤)) le_top := by
      rw [Scheme.Hom.app_eq_appLE κ.hom, Scheme.Hom.appLE_comp_appLE]
    show ((Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
          ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top ≫
        κ.hom.app ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤))
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) =
      ((κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
          (κ.hom ⁻¹ᵁ ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤)) le_top)
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    rw [hmor]

  have hbij := pullbackLocalSection_bijective κ.hom
    ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj M)
    ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) (image_preimage_eq_of_isIso _ _)
  let θ := ((Scheme.Modules.pullbackComp κ.hom (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).hom.app M).app
    ((κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤)
  let ψ : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj M,
      (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) →ₗ[B]
      Γ((Scheme.Modules.pullback (κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B))).obj M,
        (κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) :=
    { toFun := fun y => θ (pullbackLocalSection κ.hom y)
      map_add' := fun y y' => by
        show θ (pullbackLocalSection κ.hom (y + y')) = θ (pullbackLocalSection κ.hom y) + θ (pullbackLocalSection κ.hom y')
        rw [pullbackLocalSection_def, pullbackLocalSection_def, pullbackLocalSection_def]
        erw [map_add, map_add]
      map_smul' := fun b y => by
        change θ (pullbackLocalSection κ.hom
            ((((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
              (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
                ((Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top) b) • y)) =
          (((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
            (κ.hom ≫ Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)).appLE ⊤
              ((κ.hom ≫ Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R B)) ⁻¹ᵁ ⊤) le_top) b) •
            θ (pullbackLocalSection κ.hom y)
        rw [pullbackLocalSection_smul]
        erw [Scheme.Modules.Hom.app_smul]
        rw [hs] }
  have hψ : Function.Bijective ψ := (ConcreteCategory.bijective_of_isIso θ).comp hbij
  refine ⟨e₁.trans (LinearEquiv.ofBijective ψ hψ), fun b m => ?_⟩
  show ψ (e₁ (b ⊗ₜ[R] m)) = _
  rw [he₁, LinearMap.map_smul]
  congr 1
  exact Scheme.Modules.pullbackComp_hom_app_app_pullbackLocalSection κ.hom _ M ⊤ m

end S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_tensorProduct_sections_pullback_of_isPullback (solution)
