-- Prove2me | solution 1 for AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-14T18:11:14.407312+00:00
-- url     : https://prove2.me/submissions/07b6f2ee-0a36-487c-9b72-498331439a8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_regular_integral_projective_finite_cover_of_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  by_cases hdim : topologicalKrullDim X ≤ 1
  · obtain ⟨Y, a, hY, hfinite, hsurj, hreg, _, m, j, hj, hjbase⟩ :=
      AlgebraicGeometry.exists_regular_integral_projective_finite_cover_of_dimension_le_one
        K π n ι hι hdim
    letI := hfinite
    refine ⟨Y, a, hY, inferInstance, hsurj, hreg,
      ⟨⊤, ?_, inferInstance⟩, m, j, hj, hjbase⟩
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨⟨x, trivial⟩⟩
  · exact AlgebraicGeometry.exists_regular_projective_alteration_of_projective_embedding_of_one_lt_dimension
      K π n ι hι (lt_of_not_ge hdim)

#print axioms solution
