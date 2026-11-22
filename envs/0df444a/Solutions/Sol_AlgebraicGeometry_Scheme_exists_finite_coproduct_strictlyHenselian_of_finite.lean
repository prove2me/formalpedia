-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_finite_coproduct_strictlyHenselian_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T15:51:09.328992+00:00
-- url     : https://prove2.me/submissions/6d664652-acfb-4ef4-a1e4-fb27eb22280c

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing

noncomputable section

section

section

open IsLocalRing
namespace PhilipponStrictHenselianEtaleCohomology
theorem residueField_isSepClosed_of_moduleFinite {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (ResidueField B) := by
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal B)
  have : IsLocalHom (algebraMap R B) :=
    ((local_hom_TFAE (algebraMap R B)).out 4 0).mp (eq_maximalIdeal h)
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)
end PhilipponStrictHenselianEtaleCohomology

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteAlgebraComponents

universe u v

variable {I : Type v} [Fintype I] {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- The algebra factors cut out by a complete family of orthogonal idempotents. -/
def quotientProduct (e : I → B) (he : CompleteOrthogonalIdempotents e) :
    B ≃ₐ[R] ∀ i, B ⧸ Ideal.span {1 - e i} :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))
    he.bijective_pi

variable {J : Type u} [Fintype J] (e : J → B) (he : CompleteOrthogonalIdempotents e)

/-- On spectra the algebra decomposition is a coproduct of affine schemes. -/
def specCoproduct :
    (∐ fun i ↦ Spec (.of (B ⧸ Ideal.span {1 - e i}))) ≅ Spec (.of B) :=
  asIso (sigmaSpec fun i ↦ CommRingCat.of (B ⧸ Ideal.span {1 - e i})) ≪≫
    Scheme.Spec.mapIso (quotientProduct (R := B) e he).toRingEquiv.toCommRingCatIso.op

/-- Each component maps into the original spectrum by its quotient map. -/
@[reassoc]
theorem inclusion_specCoproduct (i : J) :
    Sigma.ι (fun j ↦ Spec (.of (B ⧸ Ideal.span {1 - e j}))) i ≫ (specCoproduct e he).hom =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e i}))) := by
  change Sigma.ι _ i ≫ (sigmaSpec _) ≫ Spec.map _ = _
  rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  rfl

section FiniteMorphisms

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]

/-- An affine finite morphism over a strictly henselian base decomposes into
strictly henselian local components using the algebra decomposition and
inheritance of henselianity for finite local algebras. -/
theorem exists_coproduct_strictlyHenselian_of_finite
    (decompose : ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      ∃ (_ : Fintype (MaximalSpectrum S)) (e : MaximalSpectrum S → S),
        CompleteOrthogonalIdempotents e ∧
          ∀ i, IsLocalRing (S ⧸ Ideal.span {1 - e i}))
    (henselian : ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [IsLocalRing S],
      HenselianLocalRing S)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsFinite p] :
    ∃ (ι : Type u) (_ : Fintype ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
      (h : ∀ i, HenselianLocalRing (T i)),
      (∀ i, let _ := h i; IsSepClosed (IsLocalRing.ResidueField (T i))) ∧
        ∃ (c : (∐ fun i ↦ Spec (.of (T i))) ≅ Y),
          ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (T j))) i ≫ c.hom) := by
  have : IsAffine Y := isAffine_of_isAffineHom p
  let g := Spec.preimage (Y.isoSpec.inv ≫ p)
  let S := Γ(Y, ⊤)
  let _ : Algebra R S := g.hom.toAlgebra
  have hg : IsFinite (Spec.map g) := by
    rw [Spec.map_preimage]
    infer_instance
  let _ : Module.Finite R S := (RingHom.finite_algebraMap (A := R) (B := S)).mp
    ((IsFinite.SpecMap_iff g).mp hg)
  obtain ⟨_, e, he, hLocal⟩ := decompose S
  let T (i : MaximalSpectrum S) := S ⧸ Ideal.span {1 - e i}
  have h (i : MaximalSpectrum S) : HenselianLocalRing (T i) := by
    let _ : IsLocalRing (T i) := hLocal i
    exact henselian (T i)
  have hSep (i : MaximalSpectrum S) : let _ := h i; IsSepClosed (IsLocalRing.ResidueField (T i)) := by
    let _ := h i
    exact PhilipponStrictHenselianEtaleCohomology.residueField_isSepClosed_of_moduleFinite
      (R := R) (B := T i)
  refine ⟨MaximalSpectrum S, inferInstance, T, inferInstance, h, hSep,
    specCoproduct e he ≪≫ Y.isoSpec.symm, ?_⟩
  intro i
  change IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (T j))) i ≫
    ((specCoproduct e he).hom ≫ Y.isoSpec.inv))
  rw [← Category.assoc, inclusion_specCoproduct]
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e i}))) Ideal.Quotient.mk_surjective
  infer_instance

end FiniteMorphisms

end PhilipponFiniteAlgebraComponents

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsFinite p] :
    ∃ (ι : Type u) (_ : Fintype ι) (T : ι → Type u) (_ : ∀ i, CommRing (T i))
      (h : ∀ i, HenselianLocalRing (T i)),
      (∀ i, let _ := h i; IsSepClosed (IsLocalRing.ResidueField (T i))) ∧
        ∃ (c : (∐ fun i ↦ Spec (.of (T i))) ≅ Y),
          ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (T j))) i ≫ c.hom) := by
  apply PhilipponFiniteAlgebraComponents.exists_coproduct_strictlyHenselian_of_finite R ?_ ?_ p
  · intro S _ _ _
    obtain ⟨_, e, he, _, _, h⟩ := HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite (R := R) (S := S)
    exact ⟨inferInstance, e, he, h⟩
  · intro S _ _ _ _
    exact HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S := S)

end

end
