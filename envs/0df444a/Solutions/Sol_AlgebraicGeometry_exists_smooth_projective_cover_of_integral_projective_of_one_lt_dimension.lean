-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T16:35:14.657487+00:00
-- url     : https://prove2.me/submissions/105ecd5a-b00d-4166-b7bd-434ac9230f05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_exists_normal_integral_projective_finite_cover
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by
  obtain ⟨Y, ν, hY, hnormal, hν, hsurj, hd, m, j, hj, hπ⟩ :=
    AlgebraicGeometry.exists_normal_integral_projective_finite_cover K π n i hi
  letI := hY
  letI := hν
  letI := hsurj
  letI := hj
  haveI : IsProper (ν ≫ π) := inferInstance
  obtain ⟨Z, f, hZ, hp, hs, hsm, l, k, hk, hbase⟩ :=
    AlgebraicGeometry.exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension
      K (ν ≫ π) m j hπ hnormal (by rw [hd]; exact hdim)
  letI := hp
  letI := hs
  refine ⟨Z, f ≫ ν, hZ, inferInstance, inferInstance, ?_, l, k, hk, ?_⟩
  · simpa only [Category.assoc] using hsm
  · simpa only [Category.assoc] using hbase
