-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d8d33c2d-14bb-5aa2-876e-edef2791d37b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ))
        (pt : ∀ (A : Type) [CommRing A],
          Point A n (hilbertFunctionOf n P m) ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
        (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)),
            ∃ y : Point B n (hilbertFunctionOf n P m), y.I = Ideal.map (MvPolynomial.map φ) x.I) ∧
        (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)) (y : Point B n (hilbertFunctionOf n P m)),
            y.I = Ideal.map (MvPolynomial.map φ) x.I ↔
            pt B y = Spec.map (CommRingCat.ofHom φ) ≫ pt A x) ∧
        (∀ (A : Type) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
            pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
        IsProper p ∧ LocallyOfFinitePresentation p ∧
        (∀ F : Finset Hilb, ∃ U : Hilb.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
        ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
          IsClosedImmersion ι ∧ ι ≫ ProjSpace.π ℤ N = p := by
  obtain ⟨D₀, hD₀⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
      n P hP
  refine ⟨D₀, fun m hm => ?_⟩
  obtain ⟨hbc, Hilb, pt, hnat, N, ι, hι⟩ := hD₀ m hm
  haveI : IsClosedImmersion ι := hι

  refine ⟨Hilb, ι ≫ ProjSpace.π ℤ N, pt, hbc, ?_, ?_, ?_, ?_, ?_, N, ι, hι, rfl⟩
  ·
    intro A B _ _ φ x y
    refine ⟨hnat A B φ x y, fun h => ?_⟩
    obtain ⟨y', hy'⟩ := hbc A B φ x
    have hyy' : y' = y := (pt B).injective ((hnat A B φ x y' hy').trans h.symm)
    rw [← hyy']
    exact hy'
  ·
    intro A _ x
    exact specZIsTerminal.hom_ext _ _
  ·
    infer_instance
  ·
    haveI : IsNoetherianRing (CommRingCat.of ℤ) := inferInstanceAs (IsNoetherianRing ℤ)
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of ℤ)) := inferInstance
    infer_instance
  ·
    intro F
    exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ) ι F

end S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_isProper_locallyOfFinitePresentation_hilbertFunctionOf (solution)
