-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d54f8bfb-3cf4-5652-b691-2bd73135a81b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
import Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
          (x : Point A n (hilbertFunctionOf n P m)),
          ∃ y : Point B n (hilbertFunctionOf n P m), y.I = Ideal.map (MvPolynomial.map φ) x.I) ∧
      ∃ (Hilb : Scheme.{0})
        (pt : ∀ (A : Type) [CommRing A],
          Point A n (hilbertFunctionOf n P m) ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
        (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
            (x : Point A n (hilbertFunctionOf n P m)) (y : Point B n (hilbertFunctionOf n P m)),
            y.I = Ideal.map (MvPolynomial.map φ) x.I →
            pt B y = Spec.map (CommRingCat.ofHom φ) ≫ pt A x) ∧
        ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
          IsClosedImmersion ι := by
  obtain ⟨D₀, hD⟩ := MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval n P hP
  refine ⟨D₀, fun m hm => ?_⟩

  have hlow : ∀ d, d < m → hilbertFunctionOf n P m d = Nat.choose (n + d) n := by
    intro d hd
    simp [hilbertFunctionOf, hd]
  have hcast : ∀ e, m ≤ e → (hilbertFunctionOf n P m e : ℚ) = P.eval (e : ℚ) := by
    intro e he
    obtain ⟨K, _, J, -, hJe, -⟩ := (hD e (le_trans hm he)).2
    have hnot : ¬ e < m := not_lt.mpr he
    simp only [hilbertFunctionOf, hnot, if_false]
    rw [← hJe, Int.floor_natCast, Int.toNat_natCast]
  have hcast' : ∀ e, m ≤ e → (hilbertFunctionOf n P m (e + 1) : ℚ) = P.eval ((e : ℚ) + 1) := by
    intro e he
    have := hcast (e + 1) (by omega)
    simpa [Nat.cast_succ] using this
  have h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = hilbertFunctionOf n P m e →
      Module.finrank K (piece J (e + 1)) ≤ hilbertFunctionOf n P m (e + 1) := by
    intro e he K _ J hs hJe
    have h1 := (hD e (le_trans hm he)).1 K J hs (by rw [hJe, hcast e he])
    rw [← hcast' e he] at h1
    exact_mod_cast h1
  have h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = hilbertFunctionOf n P m e ∧
      Module.finrank K (piece J (e + 1)) = hilbertFunctionOf n P m (e + 1) := by
    intro e he
    obtain ⟨K, inst, J, hs, hJe, hJe1⟩ := (hD e (le_trans hm he)).2
    refine ⟨K, inst, J, hs, ?_, ?_⟩
    · have : (Module.finrank K (piece J e) : ℚ) = hilbertFunctionOf n P m e := by rw [hJe, hcast e he]
      exact_mod_cast this
    · have : (Module.finrank K (piece J (e + 1)) : ℚ) = hilbertFunctionOf n P m (e + 1) := by
        rw [hJe1, hcast' e he]
      exact_mod_cast this
  exact AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
    n m (hilbertFunctionOf n P m) hlow h₂ h₃

end S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf (solution)
