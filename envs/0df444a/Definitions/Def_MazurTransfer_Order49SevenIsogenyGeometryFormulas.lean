-- Prove2me | Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
-- name    : MazurTransfer_Order49SevenIsogenyGeometryFormulas
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T02:52:58.119253+00:00
-- url     : https://prove2.me/theorems/4b174966-6086-4bb0-8391-3da269861c92
-- title:
--   Exact rational seven-isogeny coordinate and parameter formulas
-- statement:
--   Exact rational coordinate, kernel, Fricke and residual parameter definitions; point constructors and their geometric proofs are excluded
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution retained. Fifteen exact pure coordinate, kernel, Fricke and residual-parameter definitions selected by original kernel dependencies and complete Lean AST ranges. All fifteen values, including the decidable kernel predicate instance, have reflexive equalities checked against their original WIP values with standard axioms. Geometric equation theorems and point constructors are not embedded as data. Named downstream consumers: original seven-isogeny equation lemmas, exact point-map constructor data, residual modular relation and full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData


/- Source module: MazurTorsion.Kubert.TateNormalForm. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert









/-- The vertical tangent denominator used to normalize a marked affine
point to Tate normal form. -/
def pointTateBeta (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₃ + x * W.a₁ + 2 * y

/-- The tangent slope used in the first translation-shear of explicit Tate
normalization. -/
def pointTateLambda (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) /
    pointTateBeta W x y

/-- The quadratic coefficient after translating a marked affine point to
the origin and making its tangent horizontal. -/
def pointTateAlpha (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  W.a₂ - W.a₁ * pointTateLambda W x y + 3 * x -
    pointTateLambda W x y ^ 2





/-- The ratio `b / c` produced by explicit Tate normalization at an affine
point. -/
def pointTateParameter (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  -pointTateAlpha W x y ^ 3 /
    (pointTateBeta W x y *
      (pointTateBeta W x y - pointTateAlpha W x y *
        (W.a₁ + 2 * pointTateLambda W x y)))


















end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenHauptmodul. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The level-seven Hauptmodul obtained by explicit Tate normalization at
an affine point. -/
def orderSevenHauptmodulAt
    (W : WeierstrassCurve ℚ) (x y : ℚ) : ℚ :=
  let d := pointTateParameter W x y
  49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)





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




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert















/-- The Fricke/backtracking Hauptmodul on the quotient family.  It is
`49 / t₇` for the source-family Hauptmodul. -/
@[expose] def orderSevenFrickeParameter (d : ℚ) : ℚ :=
  (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) / (d * (d - 1))
















/-- The abscissa of the explicit Vélu map away from its three kernel
abscissae. -/
@[expose] def orderSevenVeluX (d x : ℚ) : ℚ :=
  x + (d ^ 2 * (d - 1) * (d ^ 2 - d - 1)) / x +
    (d ^ 4 * (d - 1) ^ 2) / x ^ 2 +
    (d ^ 3 * (d - 1) ^ 2 * (d ^ 2 + d - 1)) /
      (x - MazurTorsion.Kubert.orderSevenB d) +
    (d ^ 6 * (d - 1) ^ 4) / (x - MazurTorsion.Kubert.orderSevenB d) ^ 2 +
    (d * (d - 1) ^ 3 * (d ^ 2 - 3 * d + 1)) /
      (x - MazurTorsion.Kubert.orderSevenC d) +
    (d ^ 2 * (d - 1) ^ 6) / (x - MazurTorsion.Kubert.orderSevenC d) ^ 2

/-- The rational differential factor of the explicit Vélu abscissa. -/
@[expose] def orderSevenVeluDifferential (d x : ℚ) : ℚ :=
  1 - (d ^ 2 * (d - 1) * (d ^ 2 - d - 1)) / x ^ 2 -
    2 * (d ^ 4 * (d - 1) ^ 2) / x ^ 3 -
    (d ^ 3 * (d - 1) ^ 2 * (d ^ 2 + d - 1)) /
      (x - MazurTorsion.Kubert.orderSevenB d) ^ 2 -
    2 * (d ^ 6 * (d - 1) ^ 4) / (x - MazurTorsion.Kubert.orderSevenB d) ^ 3 -
    (d * (d - 1) ^ 3 * (d ^ 2 - 3 * d + 1)) /
      (x - MazurTorsion.Kubert.orderSevenC d) ^ 2 -
    2 * (d ^ 2 * (d - 1) ^ 6) / (x - MazurTorsion.Kubert.orderSevenC d) ^ 3

/-- The ordinate of the explicit Vélu map, normalized to preserve the
invariant differential. -/
@[expose] def orderSevenVeluY (d x y : ℚ) : ℚ :=
  (orderSevenVeluDifferential d x *
        (2 * y + (1 - MazurTorsion.Kubert.orderSevenC d) * x - MazurTorsion.Kubert.orderSevenB d) -
      (1 - MazurTorsion.Kubert.orderSevenC d) * orderSevenVeluX d x +
      MazurTorsion.Kubert.orderSevenB d) / 2



/-- The residual level-seven Hauptmodul obtained by applying explicit Tate
normalization to the Vélu image of an affine source point. -/
@[expose] def orderSevenResidualHauptmodul (d x y : ℚ) : ℚ :=
  orderSevenHauptmodulAt (MazurTorsion.Kubert.orderSevenQuotient d)
    (orderSevenVeluX d x) (orderSevenVeluY d x y)

/-- The kernel polynomial whose roots are the three affine pole
abscissae. -/
@[expose] def orderSevenKernelPolynomial (d x : ℚ) : ℚ :=
  x * (x - MazurTorsion.Kubert.orderSevenB d) * (x - MazurTorsion.Kubert.orderSevenC d)

/-- The cleared numerator of `orderSevenVeluX`; its denominator is the
square of `orderSevenKernelPolynomial`. -/
@[expose] def orderSevenVeluXNumerator (d x : ℚ) : ℚ :=
  x ^ 7 - 2 * d * (d - 1) * (d + 1) * x ^ 6 +
    d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1) *
        x ^ 5 -
    d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1) * x ^ 4 +
    d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1) * x ^ 3 -
    d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3) * x ^ 2 +
    d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3) * x +
    d ^ 10 * (d - 1) ^ 6

/-- The cleared numerator of `orderSevenVeluDifferential`; its denominator
is the cube of `orderSevenKernelPolynomial`. -/
@[expose] def orderSevenVeluDifferentialNumerator (d x : ℚ) : ℚ :=
  x ^ 9 - 3 * d * (d - 1) * (d + 1) * x ^ 8 -
    d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1) *
        x ^ 7 -
    d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1) * x ^ 6 +
    3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2) * x ^ 5 +
    d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1) * x ^ 4 +
    d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 + 30 * d + 5) *
        x ^ 3 +
    3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3) * x ^ 2 -
    d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7) * x -
    2 * d ^ 13 * (d - 1) ^ 8























/-- The three affine pole abscissae of the order-seven Vélu map. -/
@[expose] def OrderSevenKernelX (d x : ℚ) : Prop :=
  x = 0 ∨ x = MazurTorsion.Kubert.orderSevenB d ∨ x = MazurTorsion.Kubert.orderSevenC d

public instance orderSevenKernelXDecidable (d x : ℚ) :
    Decidable (OrderSevenKernelX d x) := by
  unfold OrderSevenKernelX
  infer_instance



























































end MazurTorsion.Kubert

end

#print axioms MazurTorsion.Kubert.OrderSevenKernelX
#print axioms MazurTorsion.Kubert.orderSevenFrickeParameter
#print axioms MazurTorsion.Kubert.orderSevenHauptmodulAt
#print axioms MazurTorsion.Kubert.orderSevenKernelPolynomial
#print axioms MazurTorsion.Kubert.orderSevenKernelXDecidable
#print axioms MazurTorsion.Kubert.orderSevenResidualHauptmodul
#print axioms MazurTorsion.Kubert.orderSevenVeluDifferential
#print axioms MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator
#print axioms MazurTorsion.Kubert.orderSevenVeluX
#print axioms MazurTorsion.Kubert.orderSevenVeluXNumerator
#print axioms MazurTorsion.Kubert.orderSevenVeluY
#print axioms MazurTorsion.Kubert.pointTateAlpha
#print axioms MazurTorsion.Kubert.pointTateBeta
#print axioms MazurTorsion.Kubert.pointTateLambda
#print axioms MazurTorsion.Kubert.pointTateParameter


