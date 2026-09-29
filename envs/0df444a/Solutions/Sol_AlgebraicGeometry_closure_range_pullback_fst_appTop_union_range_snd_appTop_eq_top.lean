-- Prove2me | solution 1 for AlgebraicGeometry.closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9d36bb6a-6feb-5bde-b3a5-cfc723548eb5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AffineProductSectionsAux

open TensorProduct

theorem closure_union_range_eq_top_of_injective {Γ Γ' A B : Type*} [CommRing Γ] [CommRing Γ'] [CommRing A] [CommRing B]
    (E : Γ →+* Γ') (hE : Function.Injective E) (F₁ : A → Γ) (F₂ : B → Γ) (X₁ X₂ : Set Γ')
    (h₁ : E '' Set.range F₁ = X₁) (h₂ : E '' Set.range F₂ = X₂) (h : Subring.closure (X₁ ∪ X₂) = ⊤) :
    Subring.closure (Set.range F₁ ∪ Set.range F₂) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : E x ∈ Subring.map E (Subring.closure (Set.range F₁ ∪ Set.range F₂)) := by
    rw [RingHom.map_closure, Set.image_union, h₁, h₂, h]; trivial
  obtain ⟨y, hy, hyx⟩ := Subring.mem_map.1 hx
  exact hE hyx ▸ hy

theorem core (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    Subring.closure
      (Set.range (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop ∪
       Set.range (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A))) (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
      = ⊤ := by
  classical
  set a := Spec.map (CommRingCat.ofHom (algebraMap R A)) with ha
  set b := Spec.map (CommRingCat.ofHom (algebraMap R B)) with hb
  let ι := pullbackSpecIso R A B

  let E : Γ(pullback a b, ⊤) →+* A ⊗[R] B := ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom).hom.comp ι.inv.appTop.hom
  have hιbij : Function.Bijective ι.inv.appTop := by
    have h1 : ∀ y, ι.hom.appTop (ι.inv.appTop y) = y := fun y => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]; rfl
    have h2 : ∀ y, ι.inv.appTop (ι.hom.appTop y) = y := fun y => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]; rfl
    exact ⟨fun y y' h => by rw [← h1 y, ← h1 y', h], fun y => ⟨_, h2 y⟩⟩
  have hEinj : Function.Injective E := by
    show Function.Injective (fun x => (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom (ι.inv.appTop x))
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom).1.comp hιbij.1
  have hE₁ : ∀ x, E ((pullback.fst a b).appTop x) =
      Algebra.TensorProduct.includeLeftRingHom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x) := by
    intro x
    have h1 : (pullback.fst a b).appTop ≫ ι.inv.appTop =
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B))).appTop := by
      rw [← Scheme.Hom.comp_appTop, pullbackSpecIso_inv_fst]
    show ((pullback.fst a b).appTop ≫ ι.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom) x = _
    rw [← Category.assoc, h1, Scheme.ΓSpecIso_naturality]
    rfl
  have hE₂ : ∀ x, E ((pullback.snd a b).appTop x) =
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom x) := by
    intro x
    have h1 : (pullback.snd a b).appTop ≫ ι.inv.appTop =
        (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) : B →+* A ⊗[R] B))).appTop := by
      rw [← Scheme.Hom.comp_appTop, pullbackSpecIso_inv_snd]
    show ((pullback.snd a b).appTop ≫ ι.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] B))).hom) x = _
    rw [← Category.assoc, h1, Scheme.ΓSpecIso_naturality]
    rfl
  apply closure_union_range_eq_top_of_injective E hEinj _ _
    (Set.range (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B))
    (Set.range (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B))
  · ext z; constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨_, (hE₁ x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2 y
      exact ⟨_, ⟨x, rfl⟩, hE₁ x⟩
  · ext z; constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨_, (hE₂ x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).2 y
      exact ⟨_, ⟨x, rfl⟩, hE₂ x⟩
  ·
    rw [Subring.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Subring.zero_mem _
    | tmul x y =>
      have : x ⊗ₜ[R] y = Algebra.TensorProduct.includeLeftRingHom x * (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) y := by
        show x ⊗ₜ[R] y = x ⊗ₜ[R] (1 : B) * (1 : A) ⊗ₜ[R] y
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨x, rfl⟩)) (Subring.subset_closure (Or.inr ⟨y, rfl⟩))
    | add x y hx hy => exact Subring.add_mem _ hx hy

end AffineProductSectionsAux

open AffineProductSectionsAux in
theorem solution
    {S : Scheme.{u}} [IsAffine S] {A B : CommRingCat.{u}} (a : Spec A ⟶ S) (b : Spec B ⟶ S) :
    Subring.closure
      (Set.range (pullback.fst a b).appTop ∪ Set.range (pullback.snd a b).appTop) = ⊤ := by
  classical

  let R : CommRingCat := Γ(S, ⊤)
  let α : R ⟶ A := Spec.preimage (a ≫ S.isoSpec.hom)
  let β : R ⟶ B := Spec.preimage (b ≫ S.isoSpec.hom)
  have hα : Spec.map α = a ≫ S.isoSpec.hom := Spec.map_preimage _
  have hβ : Spec.map β = b ≫ S.isoSpec.hom := Spec.map_preimage _
  letI : Algebra R A := α.hom.toAlgebra
  letI : Algebra R B := β.hom.toAlgebra
  have hα' : Spec.map (CommRingCat.ofHom (algebraMap R A)) = a ≫ S.isoSpec.hom := hα
  have hβ' : Spec.map (CommRingCat.ofHom (algebraMap R B)) = b ≫ S.isoSpec.hom := hβ
  let a₀ := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b₀ := Spec.map (CommRingCat.ofHom (algebraMap R B))

  let κ : pullback a b ⟶ pullback a₀ b₀ :=
    pullback.map a b a₀ b₀ (𝟙 _) (𝟙 _) S.isoSpec.hom (by rw [Category.id_comp]; exact hα'.symm)
      (by rw [Category.id_comp]; exact hβ'.symm)
  haveI hκ : IsIso κ := by dsimp only [κ]; infer_instance

  have hκbij : Function.Bijective κ.appTop := by
    have h1 : ∀ y, κ.appTop ((inv κ).appTop y) = y := fun y => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]; rfl
    have h2 : ∀ y, (inv κ).appTop (κ.appTop y) = y := fun y => by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop]; rfl
    exact ⟨fun y y' h => by rw [← h2 y, ← h2 y', h], fun y => ⟨_, h1 y⟩⟩

  have hκ1 : κ ≫ pullback.fst a₀ b₀ = pullback.fst a b := by
    show pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_fst, Category.comp_id]
  have hκ2 : κ ≫ pullback.snd a₀ b₀ = pullback.snd a b := by
    show pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_snd, Category.comp_id]
  have hfst : ∀ x, (pullback.fst a b).appTop x = κ.appTop ((pullback.fst a₀ b₀).appTop x) := fun x => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hκ1]
  have hsnd : ∀ x, (pullback.snd a b).appTop x = κ.appTop ((pullback.snd a₀ b₀).appTop x) := fun x => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hκ2]

  have hcore := core R A B
  rw [Subring.eq_top_iff']
  intro y
  obtain ⟨x, rfl⟩ := hκbij.2 y
  have hx : x ∈ Subring.closure (Set.range (pullback.fst a₀ b₀).appTop ∪ Set.range (pullback.snd a₀ b₀).appTop) := by
    rw [hcore]; trivial
  have : κ.appTop.hom x ∈ Subring.map κ.appTop.hom
      (Subring.closure (Set.range (pullback.fst a₀ b₀).appTop ∪ Set.range (pullback.snd a₀ b₀).appTop)) :=
    Subring.mem_map.2 ⟨x, hx, rfl⟩
  rw [RingHom.map_closure, Set.image_union] at this
  refine Subring.closure_mono ?_ this
  apply Set.union_subset_union
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩; exact ⟨z, hfst z⟩
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩; exact ⟨z, hsnd z⟩

end S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top (solution)
