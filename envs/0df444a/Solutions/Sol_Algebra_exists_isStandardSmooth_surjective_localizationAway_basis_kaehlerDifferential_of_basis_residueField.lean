-- Prove2me | solution 1 for Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4b9f595a-8dbc-54d1-b416-e443faecdd9d

import Mathlib
import Theorems.Thm_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
import Theorems.Thm_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField

set_option autoImplicit false

open TensorProduct KaehlerDifferential MvPolynomial

universe u

namespace MinimalAmbient

theorem main
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) := by
  obtain ⟨m, x, h, hsurj, hh, hdet⟩ :=
    Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField u w b₀ hb₀
  set Δ : MvPolynomial (ι ⊕ Fin m) R := Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)) with hΔ
  set g : S := MvPolynomial.aeval (Sum.elim w x) Δ with hg
  obtain ⟨C, _, _, φ, hsm, hφh, hφΔ, huniv, b, hb⟩ :=
    MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential h

  let Sg := Localization.Away g
  let ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] Sg :=
    (IsScalarTower.toAlgHom R S Sg).comp (MvPolynomial.aeval (Sum.elim w x))
  have hψ : ∀ p, ψ p = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := fun p => rfl
  have hψh : ∀ a, ψ (h a) = 0 := fun a => by rw [hψ, hh a, map_zero]
  have hψΔ : IsUnit (ψ Δ) := by
    rw [hψ]
    exact IsLocalization.Away.algebraMap_isUnit (S := Sg) g
  obtain ⟨χ, hχ⟩ := huniv Sg ψ hψh hψΔ
  letI : Algebra C Sg := χ.toRingHom.toAlgebra
  haveI : IsScalarTower R C Sg := IsScalarTower.of_algebraMap_eq fun r => (χ.commutes r).symm
  refine ⟨g, hdet, C, inferInstance, inferInstance, inferInstance, inferInstance, hsm, ?_,
    fun i => φ (MvPolynomial.X (Sum.inl i)), b, ?_, hb⟩
  ·
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
    obtain ⟨p, rfl⟩ := hsurj s
    obtain ⟨v, hv⟩ := hφΔ
    refine ⟨φ p * ((v⁻¹ : Cˣ) : C) ^ k, ?_⟩
    change χ (φ p * ((v⁻¹ : Cˣ) : C) ^ k) = _
    rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_pow]
    have h1 : χ (φ p) = algebraMap S Sg (MvPolynomial.aeval (Sum.elim w x) p) := by
      rw [← hψ, ← hχ]; rfl
    have h2 : χ ((v⁻¹ : Cˣ) : C) * algebraMap S Sg g = 1 := by
      have : χ (v : C) = algebraMap S Sg g := by rw [hv, ← hψ Δ, ← hχ]; rfl
      rw [← this, ← map_mul, Units.inv_mul, map_one]
    rw [h1, ← hk, map_pow, mul_assoc, ← mul_pow, h2, one_pow, mul_one]
  · intro i
    change χ (φ (MvPolynomial.X (Sum.inl i))) = _
    rw [show χ (φ (MvPolynomial.X (Sum.inl i))) = ψ (MvPolynomial.X (Sum.inl i)) by rw [← hχ]; rfl, hψ,
      MvPolynomial.aeval_X, Sum.elim_inl]

end MinimalAmbient

theorem solution
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) :=
  MinimalAmbient.main u w b₀ hb₀

end S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
end P2MW
export P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField (solution)
