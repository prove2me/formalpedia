-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7239b0c6-df3e-5cc2-ac33-5f9f16995e77

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f]
    (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  classical
  let P : Scheme.{0} := pullback f y
  let g : P ⟶ Spec (CommRingCat.of k) := pullback.snd f y
  haveI : IsIntegralHom g := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom g

  obtain ⟨t⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨x₀, hx₀⟩ := f.surjective (y t)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x₀ t hx₀

  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of k ⟶ A := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop
  have hφ : φ.hom.IsIntegral := by
    have h := ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom) (f := g)).mp inferInstance).2
    have h' : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.IsIntegral :=
      RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).surjective
    have h__af := RingHom.IsIntegral.trans _ _ h' h
    simp only [φ, CommRingCat.hom_comp] at h__af
    exact h__af
  haveI : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨P.isoSpec.hom z⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A

  letI : Algebra k A := φ.hom.toAlgebra
  letI : Algebra k (A ⧸ 𝔪) := ((Ideal.Quotient.mk 𝔪).comp φ.hom).toAlgebra
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Algebra.IsIntegral k (A ⧸ 𝔪) :=
    ⟨RingHom.IsIntegral.trans _ _ hφ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)⟩
  haveI : Algebra.IsAlgebraic k (A ⧸ 𝔪) := inferInstance
  let ψ : (A ⧸ 𝔪) →ₐ[k] k := IsAlgClosed.lift
  let χ : A →+* k := ψ.toRingHom.comp (Ideal.Quotient.mk 𝔪)
  have hχ : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := by
    ext a
    change ψ ((Ideal.Quotient.mk 𝔪) (φ.hom a)) = a
    exact ψ.commutes a

  let x' : Spec (CommRingCat.of k) ⟶ P := Spec.map (CommRingCat.ofHom χ) ≫ P.isoSpec.inv
  have hx' : x' ≫ g = 𝟙 _ := by
    simp only [x', Category.assoc]
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp,
      ← Category.assoc, show (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop = φ from rfl, hχ, Spec.map_id]
  refine ⟨x' ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx', Category.id_comp]

end S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective (solution)
