-- Prove2me | solution 1 for AlgebraicGeometry.exists_algEquiv_globalSections_pullback_spec_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/17759ada-7840-5aac-8016-e512006a4a6a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
set_option Elab.async false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsAffine X]
    (S : Type u) [CommRing S] [Algebra R S] :
    letI : Algebra R Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra S Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom.toAlgebra
    ∃ e : S ⊗[R] Γ(X, ⊤) ≃ₐ[S] Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S))), ⊤),
      ∀ a : Γ(X, ⊤), e (1 ⊗ₜ a) =
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop a := by
  classical
  set g := Spec.map (CommRingCat.ofHom (algebraMap R S)) with hg
  letI algA : Algebra R Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  letI algP : Algebra S Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd f g).appTop).hom.toAlgebra

  set φ : CommRingCat.of R ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop with hφ
  have hφ' : CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) = φ := by
    rw [hφ]; rfl
  set f₀ : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) with hf₀
  have hf : f = X.isoSpec.hom ≫ f₀ := by
    have h1 := Scheme.isoSpec_hom_naturality f

    have h2 : (Spec (CommRingCat.of R)).isoSpec.hom = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
      rw [Scheme.isoSpec_hom, SpecMap_ΓSpecIso_hom]
    rw [h2] at h1
    rw [hf₀, hφ', hφ, Spec.map_comp, ← Category.assoc, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]

  let ε : pullback f g ≅ Spec (CommRingCat.of (Γ(X, ⊤) ⊗[R] S)) :=
    (asIso (pullback.map f g f₀ g X.isoSpec.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hf]) (by rw [Category.comp_id, Category.id_comp]))) ≪≫
      pullbackSpecIso R Γ(X, ⊤) S
  have hε_fst : ε.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      pullback.fst f g ≫ X.isoSpec.hom := by
    simp only [ε, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [show (pullbackSpecIso R Γ(X, ⊤) S).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[R] S)) =
        pullback.fst f₀ g from pullbackSpecIso_hom_fst R Γ(X, ⊤) S, pullback.lift_fst]
  have hε_snd : ε.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      S →+* Γ(X, ⊤) ⊗[R] S)) = pullback.snd f g := by
    have h0 := pullbackSpecIso_hom_snd R Γ(X, ⊤) S
    simp only [ε, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [show (pullbackSpecIso R Γ(X, ⊤) S).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : S →+* Γ(X, ⊤) ⊗[R] S)) =
        pullback.snd f₀ g from h0, pullback.lift_snd, Category.comp_id]

  let Ψ : CommRingCat.of (Γ(X, ⊤) ⊗[R] S) ≅ Γ(pullback f g, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⊗[R] S))).symm ≪≫ Scheme.Γ.mapIso ε.op
  have hΨ : Ψ.hom = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, ⊤) ⊗[R] S))).inv ≫ ε.hom.appTop := rfl

  have hΨ_left : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ Ψ.hom = (pullback.fst f g).appTop := by
    have h := congrArg Scheme.Hom.appTop hε_fst
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h

    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[R] S))

    rw [hΨ, ← Category.assoc, hn, Category.assoc, h, ← Category.assoc]
    show ((Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom) ≫ _ = _
    rw [Iso.inv_hom_id, Category.id_comp]
  have hΨ_right : CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : S →+* Γ(X, ⊤) ⊗[R] S) ≫ Ψ.hom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd f g).appTop := by
    have h := congrArg Scheme.Hom.appTop hε_snd
    rw [Scheme.Hom.comp_appTop] at h
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      S →+* Γ(X, ⊤) ⊗[R] S))
    rw [hΨ, ← Category.assoc, hn, Category.assoc, h]

  let ΨE : (Γ(X, ⊤) ⊗[R] S) ≃+* Γ(pullback f g, ⊤) := Ψ.commRingCatIsoToRingEquiv
  have hΨE : ∀ z, ΨE z = Ψ.hom z := fun _ => rfl
  let E : (S ⊗[R] Γ(X, ⊤)) ≃+* Γ(pullback f g, ⊤) :=
    (Algebra.TensorProduct.comm R S Γ(X, ⊤)).toRingEquiv.trans ΨE
  have hE : ∀ (s : S) (a : Γ(X, ⊤)), E (s ⊗ₜ[R] a) = Ψ.hom (a ⊗ₜ[R] s) := fun _ _ => rfl
  have hleft : ∀ a : Γ(X, ⊤), Ψ.hom (a ⊗ₜ[R] (1 : S)) = (pullback.fst f g).appTop a := by
    intro a
    have := CommRingCat.hom_ext_iff.mp hΨ_left
    exact congrFun (congrArg DFunLike.coe this) a ▸ rfl
  have hright : ∀ s : S, Ψ.hom ((1 : Γ(X, ⊤)) ⊗ₜ[R] s) = algebraMap S Γ(pullback f g, ⊤) s := by
    intro s
    have := CommRingCat.hom_ext_iff.mp hΨ_right
    exact congrFun (congrArg DFunLike.coe this) s ▸ rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := E) (fun s => ?_), fun a => ?_⟩
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hE, hright]
  · show E ((1 : S) ⊗ₜ[R] a) = _
    rw [hE, hleft]

end S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct
end P2MW
export P2MW.S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct (solution)
