-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-24T02:29:19.844353+00:00
-- url     : https://prove2.me/submissions/9e5c5690-2986-42f9-8736-c98ccde22ed5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_curve_fibration_of_finite_smooth_proper_generic_cover

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false
set_option maxHeartbeats 100000

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {G : Scheme.{u}} [IsIntegral G]
    (π : G ⟶ Spec (.of K)) [IsProper π] (d : ℕ)
    (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K))
    [IsClosedImmersion k] (hk : k ≫ ProjSpace.π K d = π)
    (r : ℕ) (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsProper q] [Surjective q] (hr : 0 < r)
    (hbase : q ≫ ProjSpace.π K r = π)
    (hnormal : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g))
    (hdim : topologicalKrullDim G = ((r + 1 : ℕ) : WithBot ℕ∞))
    (W : G.Opens) (hW : IsAffineOpen W) (hWne : Nonempty W)
    (hWdense : Dense (W : Set G)) (hsmooth : Smooth (W.ι ≫ q))
    (η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    (hη : IsGenericPoint η Set.univ) (hC : IsIntegral (q.fiber η))
    (hCnormal : ∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z))
    (hCproper : IsProper (q.fiberToSpecResidueField η))
    (hCdim : topologicalKrullDim (q.fiber η) = 1)
    (hCstalk : ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ G),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by
  letI := hCproper
  let F : Type u := ((Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).residueField η)
  obtain ⟨E, hE, C₀, a, p, ha, hsurj, hsmooth, hp, hover⟩ :=
    AlgebraicGeometry.exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one F (AlgebraicClosure F)
      (q.fiberToSpecResidueField η) hCdim.le
  letI := hE
  letI := ha
  letI := hsurj
  letI := hsmooth
  letI := hp
  exact AlgebraicGeometry.exists_smooth_projective_cover_of_curve_fibration_of_finite_smooth_proper_generic_cover
    K π d k hk r q hr hbase hnormal hdim η hη E C₀ p a hover
