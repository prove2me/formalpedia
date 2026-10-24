-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_normal_integral_projective_of_one_lt_dimension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T21:45:48.309982+00:00
-- url     : https://prove2.me/submissions/f971339c-2d42-4883-bc50-9eb3b611ae3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_generic_curve_model
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by
  obtain ⟨r, G, p, q, hr, hG, hn, hdG, hdX, hp, hsp, hq, hsq, hbase, hW, hemb, hcurve⟩ :=
    AlgebraicGeometry.exists_normal_projective_generic_curve_model K π n i hi hnormal hdim
  letI := hG
  letI := hp
  letI := hsp
  letI := hq
  letI := hsq
  obtain ⟨d, k, hk, hkbase⟩ := hemb
  letI := hk
  obtain ⟨W, hWaff, hWne, hWdense, hWsmooth, _⟩ := hW
  obtain ⟨η, hη, hC, hCn, hCp, hCd, hCs⟩ := hcurve
  obtain ⟨Y, f, hY, hf, hfs, hsm, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration
      K (p ≫ π) d k hkbase r q hr hbase.symm hn (hdG.trans hdX)
      W hWaff hWne hWdense hWsmooth η hη hC hCn hCp hCd hCs
  letI := hf
  letI := hfs
  refine ⟨Y, f ≫ p, hY, inferInstance, inferInstance, ?_, m, j, hj, ?_⟩
  · simpa only [Category.assoc] using hsm
  · simpa only [Category.assoc] using hjbase

