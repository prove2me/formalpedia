-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.exists_finite_multisection_of_proper_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-22T17:50:09.127237+00:00
-- url     : https://prove2.me/submissions/f0ec499a-3434-4488-8500-208ee34be2f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_integral_finite_multisection_of_proper_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_smooth_finite_surjective_cover_of_integral_finite_cover

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {C Z : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (p : Z ⟶ C) [IsProper p] [Surjective p] :
    ∃ (D : Scheme.{u}) (b : D ⟶ Z),
      IsIntegral D ∧ IsProper ((b ≫ p) ≫ c) ∧
        SmoothOfRelativeDimension 1 ((b ≫ p) ≫ c) ∧
          IsFinite (b ≫ p) ∧ Surjective (b ≫ p) := by
  obtain ⟨W, i, hW, _, hgfinite, hgsurj⟩ :=
    SmoothProperCurve.exists_integral_finite_multisection_of_proper_surjective K c p
  let := hW
  let := hgfinite
  let := hgsurj
  obtain ⟨D, ν, hD, hνfinite, hνsurj, hsmooth⟩ :=
    SmoothProperCurve.exists_smooth_finite_surjective_cover_of_integral_finite_cover
      K c (i ≫ p)
  let := hνfinite
  let := hνsurj
  have hfinite : IsFinite ((ν ≫ i) ≫ p) := by
    simpa only [Category.assoc] using
      (inferInstance : IsFinite (ν ≫ (i ≫ p)))
  have hsurj : Surjective ((ν ≫ i) ≫ p) := by
    simpa only [Category.assoc] using
      (inferInstance : Surjective (ν ≫ (i ≫ p)))
  let := hfinite
  have hproper : IsProper (((ν ≫ i) ≫ p) ≫ c) := inferInstance
  refine ⟨D, ν ≫ i, hD, hproper, ?_, hfinite, hsurj⟩
  simpa only [Category.assoc] using hsmooth
