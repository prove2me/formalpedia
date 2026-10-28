-- Prove2me | solution 1 for AlgebraicGeometry.exists_smooth_projective_cover_of_compactified_geometricallyIntegral_smooth_proper_curve_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-28T18:47:10.434515+00:00
-- url     : https://prove2.me/submissions/63d51306-3dce-4d4c-b5d2-c1c03f4fd699
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_exists_alteration_with_regular_projective_compactification
import Theorems.Thm_AlgebraicGeometry_smooth_of_regular_stalks_over_perfect_field
import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem PhilipponProperOpenCompactification.isIso
    {Z Y S : Scheme.{u}} (j : Z ⟶ Y) (π : Y ⟶ S)
    [IsOpenImmersion j] [IsDominant j] [IsSeparated π]
    [IsProper (j ≫ π)] : IsIso j := by
  have : IsProper j := IsProper.of_comp j π
  have : Surjective j := inferInstance
  have : Epi j.base := (TopCat.epi_iff_surjective j.base).mpr j.surjective
  exact IsOpenImmersion.isIso j


theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}}
    [IsIntegral N] [IsIntegral G]
    (πN : N ⟶ Spec (.of K)) [IsProper πN]
    (dN : ℕ) (iN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) K))
    [IsClosedImmersion iN] (hiN : iN ≫ ProjSpace.π K dN = πN)
    (πG : G ⟶ Spec (.of K)) [IsProper πG]
    (dG : ℕ) (iG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) K))
    [IsClosedImmersion iG] (hiG : iG ≫ ProjSpace.π K dG = πG)
    (f : G ⟶ N) [IsProper f] [Surjective f] (hf : f ≫ πN = πG)
    (hnN : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x))
    (hnG : ∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x))
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (u₀ : U ⟶ N) [IsOpenImmersion u₀] [IsDominant u₀] [Smooth (u₀ ≫ πN)]
    (p : W ⟶ U) [Smooth p] [IsProper p] [Surjective p]
    [GeometricallyIntegral p] [GeometricallyConnected p]
    (t : W ⟶ G) [IsOpenImmersion t] [IsDominant t]
    (hcart : IsPullback t p f u₀)
    (hdim : ∀ η : N, IsGenericPoint η Set.univ → topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ G),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧ Smooth (a ≫ πG) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ πG := by
  obtain ⟨Z, a, hZ, ha, hdom, _hfinite, Y, πY, _hY, hπY, hreg,
    c, hc, hcdom, hcπ, m, j, hj, hjπ⟩ :=
    AlgebraicGeometry.exists_alteration_with_regular_projective_compactification K πG
  have : IsIntegral Z := hZ
  have : IsProper a := ha
  have : IsDominant a := hdom
  have : Surjective a := inferInstance
  have : IsProper πY := hπY
  have : IsOpenImmersion c := hc
  have : IsDominant c := hcdom
  have : IsProper (c ≫ πY) := by
    rw [hcπ]
    infer_instance
  have : IsIso c := PhilipponProperOpenCompactification.isIso c πY
  have : IsClosedImmersion j := hj
  have : Smooth πY :=
    AlgebraicGeometry.smooth_of_regular_stalks_over_perfect_field K πY hreg
  have hsmooth : Smooth (a ≫ πG) := by
    rw [← hcπ]
    infer_instance
  refine ⟨Z, a, hZ, ha, inferInstance, hsmooth, m, c ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjπ, hcπ]
