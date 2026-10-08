-- Prove2me | Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
-- name    : MazurTransfer_Order49SelectionEvaluationData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T22:49:14.840889+00:00
-- url     : https://prove2.me/theorems/ee359ec0-5bb3-4530-951c-8d81cae2d854
-- title:
--   Order-49 exact selection evaluation interface
-- statement:
--   These exact original rational formulas define the order-seven quotient curve, its cleared Tate selection expression, and the dual-kernel cubic. The predicate SelectionEvalCertificate records equality of that expression with the cubic times the canonical degree-33 cofactor at one rational abscissa. This boundary consists only of total mathematical definitions; it asserts no evaluation identity or resultant nonvanishing. All37 evaluation identities will be proved separately, then combined by polynomial interpolation.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers and authors retained. Fourteen exact pure definitions selected by kernel type/value dependencies and complete original Lean AST command ranges. Published exact original cofactor definitions are reused. Every original definition value compared with a namespace-separated copy using checked equalities and standard axioms. Named downstream consumers: the37 original selectionEvalAt0 through selectionEvalAt36 certificates, original selection polynomial interpolation, full three-bounded-resultant theorem, and arbitrary-E order49 exclusion.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/- Source module: MazurTorsion.EllipticCurve.DoublingCoordinates. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Denominator-free affine doubling coordinates

For a Weierstrass curve over `ℚ`, this file records compact homogeneous
numerators for the abscissa and completed ordinate of an affine double.
The formulas are proved directly from the chord-and-tangent law and are
designed for composition with explicit rational maps.
-/
section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling

/-- The completed-square cubic, equal on the curve to
`(2y + a₁x + a₃)²`. -/
def completedCubic (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆





























end MazurTorsion.Doubling

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenHauptmodulClearing. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Denominator-free Tate normalization at an order-seven point

The pointwise Tate-normalization formula is naturally a tower of rational
expressions.  This file exposes compact cleared coordinates for the final
Tate parameter and for the level-seven Hauptmodul.  Polynomial-certificate
consumers can therefore avoid expanding the normalization or carrying a
spurious nonvanishing assumption for the fully cleared denominator.
-/
section
namespace MazurTorsion.Kubert















/-- Homogenization of the cubic denominator in the level-seven
Hauptmodul. -/
def orderSevenParameterCubic (A B : ℚ) : ℚ :=
  A ^ 3 - 8 * A ^ 2 * B + 5 * A * B ^ 2 + B ^ 3

/-- Homogenization of the numerator in the level-seven Hauptmodul. -/
def orderSevenParameterHauptmodulNumerator (A B : ℚ) : ℚ :=
  49 * A * (A - B) * B



end MazurTorsion.Kubert

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogeny. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The explicit first seven-isogeny on the order-seven Tate family

For the order-seven Tate family, the six nonzero points in the marked
subgroup have abscissae `0`, `b`, and `c`, each occurring twice.  Pairing
opposite points in Vélu's formula gives a compact rational map with three
double poles.  This file records that formula, verifies that it lands on the
explicit quotient model, and treats all kernel poles as points at infinity.

The map is deliberately kept as an underlying point function.  Compatibility
with addition, or just with multiplication by seven, is a separate theorem
needed by the order-`49` tower.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The `b` parameter of the order-seven Tate family. -/
@[simp, expose] def orderSevenB (d : ℚ) : ℚ := d ^ 3 - d ^ 2

/-- The `c` parameter of the order-seven Tate family. -/
@[simp, expose] def orderSevenC (d : ℚ) : ℚ := d ^ 2 - d



/-- The normalized coefficient model produced by Vélu's formula for the
quotient by the marked order-seven subgroup. -/
@[expose] def orderSevenQuotient (d : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - orderSevenC d,
    -orderSevenB d,
    -orderSevenB d,
    -5 * d * (d - 1) * (d ^ 2 - d + 1) *
      (d ^ 3 + 2 * d ^ 2 - 5 * d + 1),
    -d * (d - 1) *
      (d ^ 9 + 9 * d ^ 8 - 37 * d ^ 7 + 70 * d ^ 6 -
        132 * d ^ 5 + 211 * d ^ 4 - 182 * d ^ 3 +
        76 * d ^ 2 - 18 * d + 1)⟩




























































































































end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingSelection. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Polynomial selection for backtracking through the order-seven isogeny

If Tate normalization of a point on the order-seven quotient produces the
Fricke partner of the source parameter, clearing the two Hauptmodul
expressions gives a polynomial equation.  The raw equation depends on both
affine coordinates.  On the quotient curve, completed-square identities
replace it by a compact polynomial depending only on the abscissa.

The final theorem packages the exact-order-`49` consumer: the explicit
Vélu image of such a point is not a kernel pole, lies on the quotient, and
its abscissa satisfies the selection polynomial whenever the two
Hauptmodul parameters agree.
-/
section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert





/-- Twice the completed tangent numerator at an affine point. -/
def pointTateCompletedTangentNumerator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  6 * x ^ 2 + W.b₂ * x + W.b₄

/-- An abscissa-only cleared numerator for `pointTateAlpha`, rescaled by
four on the curve. -/
def pointTateAlphaUnivariateCleared
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  (12 * x + W.b₂) * Doubling.completedCubic W x -
    pointTateCompletedTangentNumerator W x ^ 2

/-- An abscissa-only cleared last normalization factor, rescaled by four
on the curve. -/
def pointTateGammaUnivariateCleared
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  4 * Doubling.completedCubic W x ^ 2 -
    pointTateAlphaUnivariateCleared W x *
      pointTateCompletedTangentNumerator W x

/-- The abscissa-only numerator of the cleared Tate parameter. -/
def pointTateParameterUnivariateNumerator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  -pointTateAlphaUnivariateCleared W x ^ 3

/-- The abscissa-only denominator of the cleared Tate parameter. -/
def pointTateParameterUnivariateDenominator
    (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  16 * pointTateGammaUnivariateCleared W x *
    Doubling.completedCubic W x ^ 2













/-- The compact abscissa-only selection polynomial on the order-seven
quotient. -/
def orderSevenSelectionPolynomial (d X : ℚ) : ℚ :=
  let W := orderSevenQuotient d
  let A := pointTateParameterUnivariateNumerator W X
  let B := pointTateParameterUnivariateDenominator W X
  d * (d - 1) * orderSevenParameterHauptmodulNumerator A B -
    (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) *
      orderSevenParameterCubic A B







end MazurTorsion.Kubert

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenDualKernel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The dual-kernel cubic for the order-seven isogeny

The cubic below is characterized in `OrderSevenDualKernelPullback`: after
substitution of the explicit Vélu abscissa and clearing its kernel
denominator, it becomes the source seventh division polynomial.  This is the
pullback identity for the kernel of the dual isogeny.  The present file
records the cubic and proves that it has no rational root on a nonsingular
member of the source family.

The proof makes the fixed real-cyclotomic cubic
`z³ + z² - 2z - 1` appear by an explicit rational change of primitive
element.  That cubic has no rational root by the rational-root theorem.
-/
section
namespace MazurTorsion.Kubert







/-- The cubic whose geometric roots are the three nonzero abscissae of the
dual kernel of the explicit order-seven isogeny. -/
def orderSevenDualKernelPolynomial (d x : ℚ) : ℚ :=
  7 * x ^ 3 +
    (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) * x ^ 2 +
    (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 - 203 * d ^ 4 +
      49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) * x +
    (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 - 767 * d ^ 8 +
      2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 - 295 * d ^ 4 -
      116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1)















end MazurTorsion.Kubert

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingCertificateData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Polynomial data for the order-seven backtracking certificates

This file stores the degree-33 selection cofactor and the three canonical
degree-seven quotient cofactors as nested polynomials in `ℚ[D][X]`.  The
pointwise `ℚ[X]` factors are obtained only by specializing the inner parameter
variable, so the large coefficient tables have a single source of truth.

The quotient factors are ordered by constant-term `D`-valuation `3`, `2`, and
`1`; this is the canonical order used by the FLINT resultant computation.

## Computational provenance

The coefficient tables were generated with SymPy polynomial arithmetic over
`ℚ[x,d]`.  The computation expanded the order-seven Tate and selection
formulas, formed the selection numerator and the quotient seventh division
polynomial, divided each exactly by the displayed dual-kernel cubic, factored
the quotient cofactor, and sorted its three factors by constant-term
`d`-valuation `3`, `2`, and `1`.  SymPy specialization at the integer
abscissas emitted the Horner expressions in the evaluation shards.  The Lean
`ring` proofs in those shards and the interpolation argument in the final
certificate check the emitted data; they do not trust the generating script.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal





end Internal

























































namespace Internal
















































/-- Internal datum. -/ def SelectionEvalCertificate (d n : ℚ) : Prop :=
  orderSevenSelectionPolynomial d n =
    64 ^ 3 * orderSevenDualKernelPolynomial d n *
      (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d).eval n





end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end

#print axioms MazurTorsion.Doubling.completedCubic
#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.SelectionEvalCertificate
#print axioms MazurTorsion.Kubert.orderSevenB
#print axioms MazurTorsion.Kubert.orderSevenC
#print axioms MazurTorsion.Kubert.orderSevenDualKernelPolynomial
#print axioms MazurTorsion.Kubert.orderSevenParameterCubic
#print axioms MazurTorsion.Kubert.orderSevenParameterHauptmodulNumerator
#print axioms MazurTorsion.Kubert.orderSevenQuotient
#print axioms MazurTorsion.Kubert.orderSevenSelectionPolynomial
#print axioms MazurTorsion.Kubert.pointTateAlphaUnivariateCleared
#print axioms MazurTorsion.Kubert.pointTateCompletedTangentNumerator
#print axioms MazurTorsion.Kubert.pointTateGammaUnivariateCleared
#print axioms MazurTorsion.Kubert.pointTateParameterUnivariateDenominator
#print axioms MazurTorsion.Kubert.pointTateParameterUnivariateNumerator


