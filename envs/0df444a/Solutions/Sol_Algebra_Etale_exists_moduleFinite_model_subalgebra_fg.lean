-- Prove2me | solution 1 for Algebra.Etale.exists_moduleFinite_model_subalgebra_fg
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T17:49:37.594796+00:00
-- url     : https://prove2.me/submissions/3f990e28-06d2-4d6e-9506-1ef9af3aa21f

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Smooth.NoetherianDescent

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct Polynomial

namespace PhilipponFiniteEtaleCoefficientDescent

open Algebra

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B]

private theorem integral_relations {ι σ : Type*} [Fintype σ]
    (P : Presentation A B ι σ) [Module.Finite A B] (i : ι) :
    ∃ q : A[X], q.Monic ∧ ∃ w : σ → MvPolynomial ι A,
      ∑ j, w j * P.relation j = Polynomial.aeval (MvPolynomial.X i) q := by
  obtain ⟨q, hq, hqzero⟩ := IsIntegral.of_finite (R := A) (P.val i)
  refine ⟨q, hq, Ideal.mem_span_range_iff_exists_fun.mp ?_⟩
  rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  exact hqzero

/-- A finite étale algebra descends to a finite étale algebra over a finitely
generated subalgebra of its base. Include the coefficients of the monic
integrality relations and their expressions in the presentation ideal. -/
theorem exists_subalgebra_fg [Etale A B] [Module.Finite A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧ Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  classical
  obtain ⟨ι, σ, _, _, P, hdim⟩ :=
    (Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp (inferInstance : Etale A B)).out
  let P' := P.toPresentation
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  choose q hq w hw using integral_relations A B P'
  let coeffs : Set A := P.coeffs ∪ (⋃ i, ↑(q i).coeffs) ∪ (⋃ i, ⋃ j, ↑(w i j).coeffs)
  have hcoeffs : coeffs.Finite :=
    (P.finite_coeffs.union (Set.finite_iUnion fun i => (q i).coeffs.finite_toSet)).union
      (Set.finite_iUnion fun i => Set.finite_iUnion fun j => (w i j).coeffs.finite_toSet)
  let A₀ := Algebra.adjoin R coeffs
  let a : A₀ →+* A := algebraMap A₀ A
  have hinj : Function.Injective a := Subtype.val_injective
  have hcoeff {x : A} (hx : x ∈ coeffs) : x ∈ Set.range a :=
    ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩
  let : P.HasCoeffs A₀ := ⟨fun _ hx => hcoeff (Or.inl (Or.inl hx))⟩
  let T := P'.ModelOfHasCoeffs A₀
  let p : Presentation A₀ T ι σ := (P.ofHasCoeffs A₀).toPresentation
  have hE : Etale A₀ T := Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨ι, σ, inferInstance, inferInstance, P.ofHasCoeffs A₀, hdim⟩
  refine ⟨A₀, T, inferInstance, inferInstance, ⟨hcoeffs.toFinset, by simp [A₀]⟩,
    hE, ?_, ⟨P'.tensorModelOfHasCoeffsEquiv A₀⟩⟩
  have haeval := p.toGenerators.aeval_val_surjective
  have htop : Algebra.adjoin A₀ (Set.range p.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact haeval
  have hIntegral (i : ι) : IsIntegral A₀ (p.val i) := by
    obtain ⟨q₀, hq₀⟩ := (Polynomial.mem_lifts (f := a) (q i)).mp
      ((Polynomial.lifts_iff_coeffs_subset_range (f := a) (q i)).mpr
        (fun x hx => hcoeff (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)))))
    have hw₀ (j : σ) : ∃ w₀ : MvPolynomial ι A₀, MvPolynomial.map a w₀ = w i j :=
      MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
        (fun x hx => hcoeff (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)))
    choose w₀ hw₀ using hw₀
    have hmap : (algebraMap A (MvPolynomial ι A)).comp a =
        (MvPolynomial.map a).comp (algebraMap A₀ (MvPolynomial ι A₀)) :=
      RingHom.ext fun x => by simp [MvPolynomial.algebraMap_eq]
    have hrel (j : σ) : (MvPolynomial.map a) (P'.relationOfHasCoeffs A₀ j) = P'.relation j :=
      P'.map_relationOfHasCoeffs A₀ j
    have hsum : ∑ j, w₀ j * P'.relationOfHasCoeffs A₀ j =
        Polynomial.aeval (MvPolynomial.X i) q₀ := by
      apply MvPolynomial.map_injective a hinj
      rw [map_sum, Polynomial.map_aeval_eq_aeval_map hmap, hq₀]
      simpa only [map_mul, hw₀, hrel, MvPolynomial.map_X] using hw i
    refine ⟨q₀, Polynomial.monic_of_injective hinj (hq₀ ▸ hq i), ?_⟩
    have hrel₀ (j : σ) : P'.relationOfHasCoeffs A₀ j = p.relation j := rfl
    change Polynomial.aeval (p.val i) q₀ = 0
    simpa only [map_sum, map_mul, hrel₀, p.aeval_val_relation, mul_zero, Finset.sum_const_zero,
      ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X] using
      (congrArg (MvPolynomial.aeval p.val) hsum).symm
  have htopIntegral : integralClosure A₀ T = ⊤ := top_unique (htop ▸ Algebra.adjoin_le
    (by rintro _ ⟨i, rfl⟩; exact hIntegral i))
  exact (Algebra.finite_iff_isIntegral_and_finiteType).mpr
    ⟨integralClosure_eq_top_iff.mp htopIntegral, inferInstance⟩

end PhilipponFiniteEtaleCoefficientDescent

end

section

open scoped TensorProduct
universe u

theorem solution
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra.Etale A B] [Module.Finite A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Algebra.Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧ Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  exact PhilipponFiniteEtaleCoefficientDescent.exists_subalgebra_fg R A B

end

end
