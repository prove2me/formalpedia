-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isAlgClosed_factor_residueField_of_range_subset_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9510e3d2-48f2-5bc6-90ba-52371c774fd3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {T : Scheme.{u}} (x : T)
    {k₁ : Type u} [Field k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T) (hs₁ : Set.range ⇑s₁ ⊆ {x})
    {k₂ : Type u} [Field k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T) (hs₂ : Set.range ⇑s₂ ⊆ {x}) :
    ∃ (ι₁ : T.residueField x ⟶ CommRingCat.of k₁) (ι₂ : T.residueField x ⟶ CommRingCat.of k₂)
      (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k₁ Ω) (_ : Algebra k₂ Ω),
      Spec.map ι₁ ≫ T.fromSpecResidueField x = s₁ ∧
      Spec.map ι₂ ≫ T.fromSpecResidueField x = s₂ ∧
      ι₁ ≫ CommRingCat.ofHom (algebraMap k₁ Ω) = ι₂ ≫ CommRingCat.ofHom (algebraMap k₂ Ω) ∧
      Spec.map (CommRingCat.ofHom (algebraMap k₁ Ω)) ≫ s₁ =
        Spec.map (CommRingCat.ofHom (algebraMap k₂ Ω)) ≫ s₂ := by
  classical

  obtain ⟨⟨x₁, ι₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField k₁ T).symm.surjective s₁
  obtain ⟨⟨x₂, ι₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField k₂ T).symm.surjective s₂
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hs₁ hs₂ ⊢
  obtain rfl : x₁ = x := by
    have := hs₁ ⟨IsLocalRing.closedPoint k₁, rfl⟩
    simpa [Scheme.fromSpecResidueField_apply] using this
  obtain rfl : x₂ = x₁ := by
    have := hs₂ ⟨IsLocalRing.closedPoint k₂, rfl⟩
    simpa [Scheme.fromSpecResidueField_apply] using this

  letI : Algebra (T.residueField x₂) k₁ := ι₁.hom.toAlgebra
  letI : Algebra (T.residueField x₂) k₂ := ι₂.hom.toAlgebra
  let S : Type u := TensorProduct (T.residueField x₂) k₁ k₂
  haveI : Nontrivial S := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let Ω : Type u := AlgebraicClosure (S ⧸ m)
  let f₁ : k₁ →+* Ω := (algebraMap (S ⧸ m) Ω).comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeLeft (R := T.residueField x₂) (S := T.residueField x₂) (A := k₁) (B := k₂)).toRingHom)
  let f₂ : k₂ →+* Ω := (algebraMap (S ⧸ m) Ω).comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := T.residueField x₂) (A := k₁) (B := k₂)).toRingHom)
  have hcomp : ι₁ ≫ CommRingCat.ofHom f₁ = ι₂ ≫ CommRingCat.ofHom f₂ := by
    ext r
    change f₁ (algebraMap (T.residueField x₂) k₁ r) = f₂ (algebraMap (T.residueField x₂) k₂ r)
    simp only [f₁, f₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  refine ⟨ι₁, ι₂, Ω, inferInstance, inferInstance, f₁.toAlgebra, f₂.toAlgebra, rfl, rfl, hcomp, ?_⟩
  change Spec.map (CommRingCat.ofHom f₁) ≫ _ = Spec.map (CommRingCat.ofHom f₂) ≫ _
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hcomp]

end S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton (solution)
