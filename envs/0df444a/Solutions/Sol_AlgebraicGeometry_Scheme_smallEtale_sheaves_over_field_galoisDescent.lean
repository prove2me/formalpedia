-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.smallEtale_sheaves_over_field_galoisDescent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T11:20:33.837631+00:00
-- url     : https://prove2.me/submissions/469603f4-1357-4e7b-a8bd-eee1696d43b7

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_36

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]
    (Λ : Type u) [CommRing Λ]
    (pt : Spec (CommRingCat.of (SeparableClosure (X.residueField x0))) ⟶ X)
    (hpt : pt = Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0)))) ≫ X.fromSpecResidueField x0)
    (g : (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0] SeparableClosure (X.residueField x0)) →
      (Over.mk pt ⟶ Over.mk pt))
    (hg : ∀ σ, (g σ).left = Spec.map (CommRingCat.ofHom
      (σ : SeparableClosure (X.residueField x0) →+* SeparableClosure (X.residueField x0))))
    (rep : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ),
      (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0] SeparableClosure (X.residueField x0)) →
        (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F →ₗ[Λ]
          ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F))
    (hrep : ∀ F σ, rep F σ =
      ((GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ)
        (⟨Functor.whiskerLeft (Scheme.Etale.forget X)
          (coyoneda.map (g σ).op)⟩ :
            Scheme.pointSmallEtale pt ⟶ Scheme.pointSmallEtale pt)).app F).hom) :
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (v : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F),
      ∃ H : Subgroup (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0)),
        IsOpen (H : Set (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0))) ∧ ∀ σ ∈ H, rep F σ v = v) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (φ : F ⟶ G) σ,
      (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom ∘ₗ rep F σ =
        rep G σ ∘ₗ (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom) ∧
    (∀ (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
      (f : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F →ₗ[Λ]
        ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj G),
      (∀ σ, f ∘ₗ rep F σ = rep G σ ∘ₗ f) →
        ∃! φ : F ⟶ G, (((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).map φ).hom = f) ∧
    ∀ (M : Type u) [AddCommGroup M] [Module Λ M]
      (ρ : Representation Λ (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
        SeparableClosure (X.residueField x0)) M),
      (∀ m : M, ∃ H : Subgroup (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0)),
        IsOpen (H : Set (SeparableClosure (X.residueField x0) ≃ₐ[X.residueField x0]
          SeparableClosure (X.residueField x0))) ∧ ∀ σ ∈ H, ρ σ m = m) →
      ∃ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
        (e : ((Scheme.pointSmallEtale pt).sheafFiber (A := ModuleCat.{u} Λ)).obj F ≃ₗ[Λ] M),
        ∀ σ v, e (rep F σ v) = ρ σ (e v) := by
  subst hpt
  have hg' : g = fun σ => Over.homMk (RamanujanPetersson.EtSheaves.galSpec x0 σ) (RamanujanPetersson.EtSheaves.galSpec_comp x0 σ) :=
    funext fun σ => Over.OverMorphism.ext (hg σ)
  subst hg'
  have hrep' : rep = fun F σ => RamanujanPetersson.EtSheaves.galRep Λ F x0 σ := by
    funext F σ
    rw [hrep F σ]
    rfl
  subst hrep'
  refine ⟨fun F v => RamanujanPetersson.EtSheaves.exists_open_fix Λ F x0 v, fun F G φ σ => RamanujanPetersson.EtSheaves.galRep_natural Λ φ x0 σ,
    fun F G f hf => ?_, fun M _ _ ρ hρ => RamanujanPetersson.EtSheaves.specField_essSurj x0 Λ ρ hρ⟩
  refine ⟨(RamanujanPetersson.EtSheaves.specField_homEquiv x0 Λ F G).symm ⟨f, hf⟩,
    congrArg Subtype.val ((RamanujanPetersson.EtSheaves.specField_homEquiv x0 Λ F G).apply_symm_apply ⟨f, hf⟩), fun ψ hψ => ?_⟩
  exact (Equiv.eq_symm_apply _).2 (Subtype.ext hψ)
