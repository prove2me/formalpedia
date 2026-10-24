-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T16:04:02.665334+00:00
-- url     : https://prove2.me/submissions/5af5aa1a-f1f5-4dd2-a094-3f663fb85fdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective_of_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π  := by
  by_cases h : topologicalKrullDim X ≤ 1
  · exact AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_dimension_le_one
      K π n i hi h
  · exact AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension
      K π n i hi (lt_of_not_ge h)
