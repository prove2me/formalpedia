-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_CauchyPi
-- name    : liuyao_ca_fd889115_k1_Analysis_CauchyPi
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:19:47.779813+00:00
-- url     : https://prove2.me/theorems/c09d417d-5133-4ea1-a223-ae80ca1ec4ed
-- title:
--   Computable analysis · CauchyPi · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/CauchyPi.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralIdentities

set_option autoImplicit true

/-!
# The full-line Cauchy integral computation of pi

This module keeps the full-line route separate from the large presentation
registry.  The program compactifies the two rational tails of
`1 / (1 + x^2)` onto `[0,1]`; at every stage its box is exactly the box of
four times the unit-interval rectangle computation.  The final comparison is
therefore a direct chain of interval certificates to the circle-area raw real.
-/

namespace ComputableAnalysis

namespace CauchyPi

/-- The unit-interval rectangle computation, scaled to the full Cauchy
integral. -/
def rectangleRaw : RealCompute :=
  IntegralIdentities.PiFromArctanIntegral
    IntegralIdentities.arctanIntegralRectangleForAtOne

theorem rectangleRaw_valid : rectangleRaw.Valid := by
  unfold rectangleRaw IntegralIdentities.PiFromArctanIntegral
  exact RealCompute.natScale_valid 4
    IntegralIdentities.arctanIntegralRectangleForAtOne_valid

theorem piCircleArea_valid : piCircleArea.Valid := by
  change RealCompute.ValidCompute piCircleArea.compute
  have hcompute : piCircleArea.compute =
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealCompute).compute := by
    funext n
    exact (ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute n).symm
  rw [hcompute]
  exact ArctanGeometry.four_arctanGeom_one_valid

/-- Four rectangle integrals of `1 / (1+t^2)` agree with the geometric
circle-area computation of pi. -/
theorem rectangleRaw_equiv_piCircleArea : rectangleRaw.Equiv piCircleArea := by
  have hscaled : rectangleRaw.Equiv
      ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealCompute) := by
    unfold rectangleRaw IntegralIdentities.PiFromArctanIntegral
    exact RealCompute.natScale_equiv 4
      IntegralIdentities.arctanIntegralRectangleForAtOne_equiv_arctanGeom_one
  exact RealCompute.equiv_trans rectangleRaw_valid
    ArctanGeometry.four_arctanGeom_one_valid
    piCircleArea_valid
    hscaled
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

/-- The full-line rational Cauchy algorithm.  Its density is split by
evenness and the reciprocal substitution before any limit is taken. -/
def raw : RealCompute := IntegralIdentities.cauchyFullLineIntegral

theorem raw_valid : raw.Valid :=
  IntegralIdentities.cauchyFullLineIntegral_valid

/-- The compactified full-line computation and the scaled unit rectangle
computation have identical rational boxes stage by stage. -/
theorem raw_compute_eq_rectangleRaw (n : Nat) :
    raw.compute n = rectangleRaw.compute n := by
  unfold raw rectangleRaw IntegralIdentities.PiFromArctanIntegral
  exact IntegralIdentities.cauchyFullLineIntegral_compute_eq_four_rectangle n

/-- The full-line Cauchy integral is a certified computation of the same pi
as the rational circle-area algorithm. -/
theorem raw_equiv_piCircleArea : raw.Equiv piCircleArea := by
  intro n
  apply (RealCompute.compareAt_overlap_iff raw piCircleArea n n).2
  rw [raw_compute_eq_rectangleRaw n]
  exact (RealCompute.compareAt_overlap_iff rectangleRaw piCircleArea n n).1
    (rectangleRaw_equiv_piCircleArea n)

/-- The bounded version splits the Cauchy kernel at zero, computes its
increasing and decreasing pieces separately, and then applies the outer
factor of two. -/
def symmetricRaw : RealCompute :=
  IntegralIdentities.piSymmetricCauchyPiecewiseIntegral

theorem symmetricRaw_valid : symmetricRaw.Valid :=
  IntegralIdentities.piSymmetricCauchyPiecewiseIntegral_valid

/-- The two-piece monotone assembly agrees with four copies of the same
unit-interval rectangle computation used by the full-line route. -/
theorem symmetricRaw_equiv_rectangleRaw : symmetricRaw.Equiv rectangleRaw := by
  have hA : IntegralIdentities.arctanIntegralRectangleForAtOne.Valid :=
    IntegralIdentities.arctanIntegralRectangleForAtOne_valid
  have hfirst : symmetricRaw.Equiv
      ((2 : Nat) * ((2 : Nat) *
        IntegralIdentities.arctanIntegralRectangleForAtOne : RealCompute) : RealCompute) := by
    unfold symmetricRaw IntegralIdentities.piSymmetricCauchyPiecewiseIntegral
    exact RealCompute.natScale_equiv 2
      IntegralIdentities.symmetricCauchyPiecewiseIntegral_equiv_two_rectangle
  have hcompose :
      ((2 : Nat) * ((2 : Nat) *
        IntegralIdentities.arctanIntegralRectangleForAtOne : RealCompute) : RealCompute).Equiv
        rectangleRaw := by
    have h := RealCompute.scaleRat_scaleRat_equiv_of_nonneg
      (2 : Rat) (2 : Rat) (by decide +kernel) (by decide +kernel)
      IntegralIdentities.arctanIntegralRectangleForAtOne hA
    have hscale (x : RealCompute) :
        ((2 : Nat) * x : RealCompute) = RealCompute.scaleRat 2 x := by
      rfl
    rw [hscale, hscale]
    simpa only [rectangleRaw, IntegralIdentities.PiFromArctanIntegral,
      show (2 : Rat) * (2 : Rat) = 4 by decide +kernel] using h
  exact RealCompute.equiv_trans symmetricRaw_valid
    (RealCompute.natScale_valid 2 (RealCompute.natScale_valid 2 hA))
    rectangleRaw_valid hfirst hcompose

/-- The bounded increasing/decreasing Cauchy calculation is independently
equivalent to the circle-area computation of pi. -/
theorem symmetricRaw_equiv_piCircleArea : symmetricRaw.Equiv piCircleArea := by
  exact RealCompute.equiv_trans symmetricRaw_valid rectangleRaw_valid
    piCircleArea_valid symmetricRaw_equiv_rectangleRaw
    rectangleRaw_equiv_piCircleArea

end CauchyPi

end ComputableAnalysis


