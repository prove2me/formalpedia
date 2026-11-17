-- Prove2me | solution 1 for Algebra.PreSubmersivePresentation.isStandardSmoothOfRelativeDimension_localizationAway_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:41.174669+00:00
-- url     : https://prove2.me/submissions/9f88f863-e93d-4a87-b568-96250e4d7cf3

import Mathlib

/-!
# Structural smoothness from selected Jacobian minors

This module supplies the generic bridge needed by affine complete
intersections such as the N25 charts.  It contains no equation-specific
computation: the only input is a finite pre-submersive presentation and,
globally, a family of its selected Jacobians spanning the unit ideal.
-/

noncomputable section

universe u

namespace Algebra.PreSubmersivePresentation

/-- Localizing the target at a selected Jacobian gives a standard-smooth
presentation with the same relative dimension as the original finite
presentation.  The added inverse variable and its defining relation
contribute zero to the presentation dimension. -/
theorem _root_.solution
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hP : P.dimension = n) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap S (Localization.Away P.jacobian)).comp
        (algebraMap R S)) := by
  let T := Localization.Away P.jacobian
  letI : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Q : Algebra.PreSubmersivePresentation S T Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway T P.jacobian
  let C : Algebra.PreSubmersivePresentation
      R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    Q.comp P
  have hJacobian : IsUnit (algebraMap S T P.jacobian) :=
    IsLocalization.map_units T
      (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let SP : Algebra.SubmersivePresentation
      R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { __ := C
      jacobian_isUnit := by
        dsimp [C, Q]
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian]
        simpa only [Algebra.smul_def] using hJacobian.mul hJacobian }
  change RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R T)
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  apply SP.isStandardSmoothOfRelativeDimension
  change C.dimension = n
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Algebra.Presentation.localizationAway T P.jacobian).dimension +
      P.dimension = n
  rw [Algebra.Presentation.localizationAway_dimension_zero, zero_add, hP]

end Algebra.PreSubmersivePresentation
