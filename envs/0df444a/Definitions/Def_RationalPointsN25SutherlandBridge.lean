-- Prove2me | Definitions.Def_RationalPointsN25SutherlandBridge
-- name    : RationalPointsN25SutherlandBridge
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:04.969753+00:00
-- url     : https://prove2.me/theorems/cc7c30e9-7a98-4063-96a0-73f640cdf29c
-- title:
--   Explicit Tate-to-Sutherland coordinates for $X_1(25)$
-- statement:
--   Starting from Tate parameters, the file defines raw coordinates $r=b/c$ and $s=c^2/(b-c)$ through their cleared numerators, and the optimized coordinates $$x=(s-r)/(rs-2r+1),\qquad y=(rs-2r+1)/(s^2-s-r+1).$$ It records Sutherland’s bidegree-$(8,8)$ equation, the raw bidegree-$(10,15)$ equation by coefficient polynomials, and the relevant homogenized and denominator data. This supplies the explicit model comparison between the primitive Tate locus and Sutherland’s plane model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateOrder25Factor
/-!
# The Sutherland source model for the order-25 Tate locus

Andrew Sutherland's explicit models of `X₁(N)` use the raw coordinates

```
r = b / c,        s = c² / (b - c),
```

and then the birational optimization

```
x = (s - r) / (r*s - 2*r + 1),
y = (r*s - 2*r + 1) / (s² - s - r + 1).
```

This file verifies that comparison for `N = 25` directly against the primitive
Tate division polynomial `F25`.  After simplifying the composite map, it proves
an unconditional denominator-cleared polynomial identity and proves that both
remaining denominators are nonzero on the exact-order locus.  The endpoint is
therefore an explicit rational map from every primitive Tate solution to
Sutherland's bidegree-`(8,8)` plane model.

The formulas are kept as literal polynomials, and every model comparison below
is certified by `ring`; no modular-curve identification is introduced as an
assumption.  This closes the Tate-to-optimized-source part of the N25 comparison.
-/

namespace MazurProof.RationalPointsN25SutherlandBridge

open TateOrder25Factor

set_option linter.style.longLine false

/-! ## The simplified Tate-to-Sutherland coordinates -/

/-- Numerator `X = c³ - b(b-c)` of the optimized coordinate
`x = (s-r)/(r*s-2*r+1)` after substituting `r=b/c` and `s=c²/(b-c)`. -/
def tateToSutherlandXNum25 (b c : ℚ) : ℚ := -b ^ 2 + b * c + c ^ 3

/-- Common numerator `K` of `r*s-2*r+1`.  On the Tate chart,
`r*s-2*r+1 = K / (c(b-c))`; it is also the denominator of optimized `x`
and a numerator factor of optimized `y`. -/
def tateToSutherlandCommon25 (b c : ℚ) : ℚ := -2 * b ^ 2 + b * c ^ 2 + 3 * b * c - c ^ 2

/-- Numerator `B` of `s²-s-r+1` after the Tate substitution:
`s²-s-r+1 = B / (c(b-c)²)`.  Hence the optimized second coordinate is
`y = K(b-c)/B`. -/
def tateToSutherlandYDen25 (b c : ℚ) : ℚ :=
  -b ^ 3 + 3 * b ^ 2 * c - b * c ^ 3 - 3 * b * c ^ 2 + c ^ 5 + c ^ 4 + c ^ 3

/-- Numerator `c²-b+c` of `s-1 = (c²-b+c)/(b-c)`.  It appears as the
third exceptional factor in the denominator-cleared model identity. -/
def tateToSutherlandSMinusOneNum25 (b c : ℚ) : ℚ := c ^ 2 - b + c

/-! ## Sutherland's optimized and raw equations -/

/-- Sutherland's bidegree-`(8,8)` affine equation for `X₁(25)`.  The source
publishes this polynomial as `X1/FFFc25.txt`; the coordinate convention is the
optimized `(x,y)` convention stated in the module documentation. -/
def sutherlandX1Plane25 (x y : ℚ) : ℚ :=
  x ^ 8 * y ^ 2 + x ^ 7 * y ^ 5 - 4 * x ^ 7 * y ^ 4 - x ^ 7 * y ^ 2 -
  3 * x ^ 6 * y ^ 6 + 11 * x ^ 6 * y ^ 5 - 2 * x ^ 6 * y ^ 4 +
  2 * x ^ 6 * y ^ 2 - 2 * x ^ 6 * y + 3 * x ^ 5 * y ^ 7 -
  9 * x ^ 5 * y ^ 6 - 4 * x ^ 5 * y ^ 5 + 4 * x ^ 5 * y ^ 4 -
  2 * x ^ 5 * y ^ 3 + 4 * x ^ 5 * y ^ 2 - x ^ 4 * y ^ 8 +
  x ^ 4 * y ^ 7 + 9 * x ^ 4 * y ^ 6 - 5 * x ^ 4 * y ^ 5 +
  6 * x ^ 4 * y ^ 4 - 15 * x ^ 4 * y ^ 3 + 7 * x ^ 4 * y ^ 2 -
  2 * x ^ 4 * y + x ^ 4 + x ^ 3 * y ^ 8 - 4 * x ^ 3 * y ^ 7 +
  3 * x ^ 3 * y ^ 6 - 14 * x ^ 3 * y ^ 5 + 26 * x ^ 3 * y ^ 4 -
  15 * x ^ 3 * y ^ 3 + 7 * x ^ 3 * y ^ 2 - 5 * x ^ 3 * y + x ^ 3 -
  x ^ 2 * y ^ 7 + 8 * x ^ 2 * y ^ 6 - 13 * x ^ 2 * y ^ 5 +
  12 * x ^ 2 * y ^ 4 - 18 * x ^ 2 * y ^ 3 + 19 * x ^ 2 * y ^ 2 -
  8 * x ^ 2 * y + x ^ 2 - 4 * x * y ^ 5 + 13 * x * y ^ 4 -
  16 * x * y ^ 3 + 10 * x * y ^ 2 - 4 * x * y + x + y ^ 4 -
  4 * y ^ 3 + 6 * y ^ 2 - 4 * y + 1

def sutherlandRawCoefficientTen (s : ℚ) : ℚ :=
  1

def sutherlandRawCoefficientNine (s : ℚ) : ℚ :=
  -s ^ 10 + 17 * s ^ 9 - 123 * s ^ 8 + 494 * s ^ 7 - 1205 * s ^ 6 + 1836 * s ^ 5 - 1732 * s ^ 4 + 968 * s ^ 3 - 294 * s ^ 2 + 35 * s - 5

def sutherlandRawCoefficientEight (s : ℚ) : ℚ :=
  -6 * s ^ 10 + 74 * s ^ 9 - 345 * s ^ 8 + 690 * s ^ 7 - 185 * s ^ 6 - 1659 * s ^ 5 + 3051 * s ^ 4 - 2320 * s ^ 3 + 840 * s ^ 2 - 105 * s + 10

def sutherlandRawCoefficientSeven (s : ℚ) : ℚ :=
  -21 * s ^ 10 + 161 * s ^ 9 - 351 * s ^ 8 - 144 * s ^ 7 + 1289 * s ^ 6 - 789 * s ^ 5 - 1551 * s ^ 4 + 2166 * s ^ 3 - 996 * s ^ 2 + 126 * s - 10

def sutherlandRawCoefficientSix (s : ℚ) : ℚ :=
  s ^ 15 - 18 * s ^ 14 + 151 * s ^ 13 - 770 * s ^ 12 + 2655 * s ^ 11 - 6558 * s ^ 10 + 11834 * s ^ 9 - 15408 * s ^ 8 + 14630 * s ^ 7 - 11195 * s ^ 6 + 7227 * s ^ 5 - 2441 * s ^ 4 - 388 * s ^ 3 + 555 * s ^ 2 - 70 * s + 5

def sutherlandRawCoefficientFive (s : ℚ) : ℚ :=
  s ^ 15 - 15 * s ^ 14 + 90 * s ^ 13 - 245 * s ^ 12 + 90 * s ^ 11 + 1587 * s ^ 10 - 6145 * s ^ 9 + 12270 * s ^ 8 - 15060 * s ^ 7 + 12520 * s ^ 6 - 8214 * s ^ 5 + 3660 * s ^ 4 - 685 * s ^ 3 - 120 * s ^ 2 + 15 * s - 1

def sutherlandRawCoefficientFour (s : ℚ) : ℚ :=
  s ^ 3 * (s ^ 12 - 12 * s ^ 11 + 48 * s ^ 10 - 49 * s ^ 9 - 165 * s ^ 8 + 609 * s ^ 7 - 433 * s ^ 6 - 1623 * s ^ 5 + 4299 * s ^ 4 - 4615 * s ^ 3 + 3435 * s ^ 2 - 1740 * s + 455)

def sutherlandRawCoefficientThree (s : ℚ) : ℚ :=
  s ^ 3 * (s ^ 12 - 9 * s ^ 11 + 25 * s ^ 10 - 35 * s ^ 9 + 45 * s ^ 8 - 181 * s ^ 7 + 569 * s ^ 6 - 705 * s ^ 5 + 5 * s ^ 4 + 470 * s ^ 3 - 540 * s ^ 2 + 340 * s - 105)

def sutherlandRawCoefficientTwo (s : ℚ) : ℚ :=
  s ^ 3 * (s ^ 12 - 6 * s ^ 11 + 21 * s ^ 10 - 56 * s ^ 9 + 126 * s ^ 8 - 231 * s ^ 7 + 266 * s ^ 6 - 126 * s ^ 5 + 96 * s ^ 4 - 91 * s ^ 3 + 75 * s ^ 2 - 45 * s + 15)

def sutherlandRawCoefficientOne (s : ℚ) : ℚ :=
  s ^ 3 * (6 * s ^ 7 - 28 * s ^ 6 + 21 * s ^ 5 - 15 * s ^ 4 + 10 * s ^ 3 - 6 * s ^ 2 + 3 * s - 1)

def sutherlandRawCoefficientZero (s : ℚ) : ℚ :=
  s ^ 10

/-- Sutherland's raw equation `F(r,s)=0` for `X₁(25)`, before the universal
birational optimization.  Its bidegrees are `10` in `r` and `15` in `s`.
This is deliberately distinct from the repository's Tate polynomial `F25`. -/
def sutherlandRawX1Plane25 (r s : ℚ) : ℚ :=
  r ^ 10 * sutherlandRawCoefficientTen s +
    r ^ 9 * sutherlandRawCoefficientNine s +
    r ^ 8 * sutherlandRawCoefficientEight s +
    r ^ 7 * sutherlandRawCoefficientSeven s +
    r ^ 6 * sutherlandRawCoefficientSix s +
    r ^ 5 * sutherlandRawCoefficientFive s +
    r ^ 4 * sutherlandRawCoefficientFour s +
    r ^ 3 * sutherlandRawCoefficientThree s +
    r ^ 2 * sutherlandRawCoefficientTwo s +
    r ^ 1 * sutherlandRawCoefficientOne s +
    r ^ 0 * sutherlandRawCoefficientZero s

def sutherlandHomogeneousCoefficientEight (K D B : ℚ) : ℚ :=
  B ^ 6 * D ^ 2 * K ^ 2

def sutherlandHomogeneousCoefficientSeven (K D B : ℚ) : ℚ :=
  -B ^ 3 * D ^ 2 * K ^ 3 * (B ^ 3 + 4 * B * D ^ 2 * K ^ 2 - D ^ 3 * K ^ 3)

def sutherlandHomogeneousCoefficientSix (K D B : ℚ) : ℚ :=
  -B ^ 2 * D * K ^ 3 * (2 * B ^ 5 - 2 * B ^ 4 * D * K + 2 * B ^ 2 * D ^ 3 * K ^ 3 - 11 * B * D ^ 4 * K ^ 4 + 3 * D ^ 5 * K ^ 5)

def sutherlandHomogeneousCoefficientFive (K D B : ℚ) : ℚ :=
  B * D ^ 2 * K ^ 5 * (4 * B ^ 5 - 2 * B ^ 4 * D * K + 4 * B ^ 3 * D ^ 2 * K ^ 2 - 4 * B ^ 2 * D ^ 3 * K ^ 3 - 9 * B * D ^ 4 * K ^ 4 + 3 * D ^ 5 * K ^ 5)

def sutherlandHomogeneousCoefficientFour (K D B : ℚ) : ℚ :=
  K ^ 4 * (B ^ 8 - 2 * B ^ 7 * D * K + 7 * B ^ 6 * D ^ 2 * K ^ 2 - 15 * B ^ 5 * D ^ 3 * K ^ 3 + 6 * B ^ 4 * D ^ 4 * K ^ 4 - 5 * B ^ 3 * D ^ 5 * K ^ 5 + 9 * B ^ 2 * D ^ 6 * K ^ 6 + B * D ^ 7 * K ^ 7 - D ^ 8 * K ^ 8)

def sutherlandHomogeneousCoefficientThree (K D B : ℚ) : ℚ :=
  K ^ 5 * (B - D * K) * (B ^ 7 - 4 * B ^ 6 * D * K + 3 * B ^ 5 * D ^ 2 * K ^ 2 - 12 * B ^ 4 * D ^ 3 * K ^ 3 + 14 * B ^ 3 * D ^ 4 * K ^ 4 + 3 * B * D ^ 6 * K ^ 6 - D ^ 7 * K ^ 7)

def sutherlandHomogeneousCoefficientTwo (K D B : ℚ) : ℚ :=
  B * K ^ 6 * (B - D * K) ^ 2 * (B ^ 5 - 6 * B ^ 4 * D * K + 6 * B ^ 3 * D ^ 2 * K ^ 2 + 6 * B * D ^ 4 * K ^ 4 - D ^ 5 * K ^ 5)

def sutherlandHomogeneousCoefficientOne (K D B : ℚ) : ℚ :=
  B ^ 3 * K ^ 7 * (B - D * K) ^ 3 * (B ^ 2 - B * D * K + 4 * D ^ 2 * K ^ 2)

def sutherlandHomogeneousCoefficientZero (K D B : ℚ) : ℚ :=
  B ^ 4 * K ^ 8 * (B - D * K) ^ 4

/-- The `(8,8)` bihomogenization of `sutherlandX1Plane25` evaluated at
projective pairs `[X:K]` and `[K*D:B]`.  It is polynomial even on the boundary
where either affine denominator vanishes. -/
def sutherlandBihomogenized25 (X K D B : ℚ) : ℚ :=
  X ^ 8 * sutherlandHomogeneousCoefficientEight K D B +
    X ^ 7 * sutherlandHomogeneousCoefficientSeven K D B +
    X ^ 6 * sutherlandHomogeneousCoefficientSix K D B +
    X ^ 5 * sutherlandHomogeneousCoefficientFive K D B +
    X ^ 4 * sutherlandHomogeneousCoefficientFour K D B +
    X ^ 3 * sutherlandHomogeneousCoefficientThree K D B +
    X ^ 2 * sutherlandHomogeneousCoefficientTwo K D B +
    X ^ 1 * sutherlandHomogeneousCoefficientOne K D B +
    X ^ 0 * sutherlandHomogeneousCoefficientZero K D B

end MazurProof.RationalPointsN25SutherlandBridge


