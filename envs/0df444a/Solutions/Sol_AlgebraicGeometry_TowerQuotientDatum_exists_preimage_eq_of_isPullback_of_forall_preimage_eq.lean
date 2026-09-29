-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_preimage_eq_of_isPullback_of_forall_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/313a63f6-37f4-52a3-95c1-f2e3261bb41f

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (X' Y' : ℕ → Scheme.{0}) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (p' : ∀ n : ℕ, X' n ⟶ Y' n) (q : ∀ n : ℕ, X' n ⟶ X n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (n : ℕ) :
    Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
    (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
    (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O) := by
  classical

  have hsurj : Surjective (p' n) := MorphismProperty.of_isPullback (P := @Surjective) (hsq n) (D.p_surjective n)
  haveI hfin : IsFinite (p' n) := MorphismProperty.of_isPullback (P := @IsFinite) (hsq n) (D.p_isFinite n)
  have hcl : IsClosedMap (p' n).base := (p' n).isClosedMap

  have horb : ∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x' := by
    intro x x' hxx
    let k₀ : CommRingCat := (Y' n).residueField ((p' n).base x)
    let k₁ : CommRingCat := (X' n).residueField x
    let k₂ : CommRingCat := (X' n).residueField x'
    let i₁ : k₀ ⟶ k₁ := (p' n).residueFieldMap x
    let i₂ : k₀ ⟶ k₂ := ((Y' n).residueFieldCongr hxx).hom ≫ (p' n).residueFieldMap x'
    letI alg₁ : Algebra k₀ k₁ := i₁.hom.toAlgebra
    letI alg₂ : Algebra k₀ k₂ := i₂.hom.toAlgebra
    haveI : Nontrivial (TensorProduct k₀ k₁ k₂) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k₀ k₁ k₂ i₁.hom.injective i₂.hom.injective
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct k₀ k₁ k₂)
    letI : Field (TensorProduct k₀ k₁ k₂ ⧸ m) := Ideal.Quotient.field m
    let K : Type := AlgebraicClosure (TensorProduct k₀ k₁ k₂ ⧸ m)
    let j : TensorProduct k₀ k₁ k₂ →+* K := (algebraMap _ K).comp (Ideal.Quotient.mk m)
    let j₁ : k₁ →+* K := j.comp (Algebra.TensorProduct.includeLeft (R := k₀) (S := k₀) (A := k₁) (B := k₂)).toRingHom
    let j₂ : k₂ →+* K := j.comp (Algebra.TensorProduct.includeRight (R := k₀) (A := k₁) (B := k₂)).toRingHom
    have hj : j₁.comp i₁.hom = j₂.comp i₂.hom := by
      ext c
      show j (Algebra.TensorProduct.includeLeft (R := k₀) (S := k₀) (A := k₁) (B := k₂) (algebraMap k₀ k₁ c)) =
        j (Algebra.TensorProduct.includeRight (R := k₀) (A := k₁) (B := k₂) (algebraMap k₀ k₂ c))
      rw [AlgHom.commutes, AlgHom.commutes]

    let ξ₁ : Spec (CommRingCat.of K) ⟶ X' n := Spec.map (CommRingCat.ofHom j₁) ≫ (X' n).fromSpecResidueField x
    let ξ₂ : Spec (CommRingCat.of K) ⟶ X' n := Spec.map (CommRingCat.ofHom j₂) ≫ (X' n).fromSpecResidueField x'
    have hξp : ξ₁ ≫ p' n = ξ₂ ≫ p' n := by
      show (Spec.map (CommRingCat.ofHom j₁) ≫ (X' n).fromSpecResidueField x) ≫ p' n =
        (Spec.map (CommRingCat.ofHom j₂) ≫ (X' n).fromSpecResidueField x') ≫ p' n
      rw [Category.assoc, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← (Y' n).residueFieldCongr_fromSpecResidueField hxx, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc]
      congr 2
      show i₁ ≫ CommRingCat.ofHom j₁ = (((Y' n).residueFieldCongr hxx).hom ≫ (p' n).residueFieldMap x') ≫ CommRingCat.ofHom j₂
      ext c
      exact congrArg (fun φ : (k₀ : Type) →+* K => φ c) hj
    have hw := (hsq n).w
    have hξY : (ξ₂ ≫ q n) ≫ D.p n = (ξ₁ ≫ q n) ≫ D.p n := by
      have h := congrArg (· ≫ r n) hξp
      simp only [Category.assoc] at h ⊢
      rw [hw, h]
    obtain ⟨g, hg⟩ := ((D.fib n K ((ξ₁ ≫ q n) ≫ D.p n)).2 (ξ₁ ≫ q n) (ξ₂ ≫ q n) rfl).mp hξY
    have hξ : ξ₁ ≫ (a' n g).hom = ξ₂ := by
      apply (hsq n).hom_ext
      · rw [Category.assoc, hq_a, ← Category.assoc, ← hg]
      · rw [Category.assoc, hp'_inv, hξp]
    refine ⟨g, ?_⟩
    have hb := congrArg (fun φ => φ.base (default : Spec (CommRingCat.of K))) hξ
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hb
    have h1 : ξ₁.base default = x := by
      show ((X' n).fromSpecResidueField x).base ((Spec.map (CommRingCat.ofHom j₁)).base default) = x
      exact (X' n).fromSpecResidueField_apply x _
    have h2 : ξ₂.base default = x' := by
      show ((X' n).fromSpecResidueField x').base ((Spec.map (CommRingCat.ofHom j₂)).base default) = x'
      exact (X' n).fromSpecResidueField_apply x' _
    rw [h1, h2] at hb
    exact hb
  refine ⟨hsurj.surj, hcl, horb, ?_⟩

  intro O hO
  refine ⟨⟨((p' n).base '' (O : Set (X' n))ᶜ)ᶜ, (hcl _ (isClosed_compl_iff.2 O.2)).isOpen_compl⟩, ?_⟩
  ext z
  change (p' n).base z ∈ ((p' n).base '' (O : Set (X' n))ᶜ)ᶜ ↔ z ∈ O
  rw [Set.mem_compl_iff, Set.mem_image]
  constructor
  · intro hz
    by_contra hzO
    exact hz ⟨z, hzO, rfl⟩
  · rintro hz ⟨z', hz', e⟩
    obtain ⟨g, rfl⟩ := horb z z' e.symm
    apply hz'
    have : z ∈ (a' n g).hom ⁻¹ᵁ O := by rw [hO]; exact hz
    exact this

end S_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq (solution)
