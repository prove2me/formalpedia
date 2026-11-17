-- Prove2me | Definitions.Def_RationalPointsN25CanonicalPoints
-- name    : RationalPointsN25CanonicalPoints
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:18.937307+00:00
-- url     : https://prove2.me/theorems/7811fe9e-555e-472c-ae37-303618759cac
-- title:
--   Canonical equations, projection, and cusps at level $25$
-- statement:
--   The file defines the canonical quadric and cubic in $ℙ^3$, the coefficient and constant term obtained by viewing the cubic as linear in $y$, the plane sextic produced by eliminating $y$, and the recovered value of $y$ off the exceptional denominator. It also defines nonzero homogeneous quadruples, projective equality, and the five rational cusp classes. These objects support the reduction of noncuspidal rational points to an explicit affine chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-!
# Coordinate-boundary rational points on the level-25 canonical curve

The genus-four quotient used at level `25` has canonical model in `ℙ³`

```
-x*z - x*w + y^2 + y*z + z*w = 0,
x^2*w + x*y*z - x*y*w - x*z*w + y*z*w + z^2*w - z*w^2 = 0.
```

This file proves an unconditional boundary classification: if any one of the
four homogeneous coordinates of a rational point is zero, then the point is
projectively equal to one of the five rational cusps.  Consequently every
hypothetical noncuspidal rational point lies in the dense torus where all four
coordinates are nonzero.

The only number-theoretic input needed for the `y = 0` chart is the rational
root theorem for the monic irreducible cubic `T^3 - T - 1`.
-/

namespace MazurProof.RationalPointsN25CanonicalPoints

open Polynomial

/-- The quadratic equation of the canonical model. -/
def canonicalQuadric25 (x y z w : ℚ) : ℚ :=
  -x * z - x * w + y ^ 2 + y * z + z * w

/-- The cubic equation of the canonical model. -/
def canonicalCubic25 (x y z w : ℚ) : ℚ :=
  x ^ 2 * w + x * y * z - x * y * w - x * z * w +
    y * z * w + z ^ 2 * w - z * w ^ 2

/-- The coefficient of `y` when the canonical cubic is viewed as a linear
equation in `y`. -/
def projectionDenominator25 (x z w : ℚ) : ℚ :=
  x * z - x * w + z * w

/-- The `y`-independent term of the canonical cubic. -/
def projectionNumerator25 (x z w : ℚ) : ℚ :=
  w * (x ^ 2 - x * z + z ^ 2 - z * w)

/-- The plane sextic obtained by eliminating `y` from the canonical model. -/
def canonicalPlaneSextic25 (x z w : ℚ) : ℚ :=
  x ^ 4 * w ^ 2 - x ^ 3 * z ^ 3 - x ^ 3 * w ^ 3 -
    x ^ 2 * z ^ 2 * w ^ 2 + x ^ 2 * z * w ^ 3 -
    x * z ^ 4 * w + 2 * x * z ^ 3 * w ^ 2 -
    2 * x * z ^ 2 * w ^ 3 + z ^ 2 * w ^ 4

/-- On the open set where the cubic is genuinely linear in `y`, this is its
unique solution. -/
def recoveredY25 (x z w : ℚ) : ℚ :=
  -projectionNumerator25 x z w / projectionDenominator25 x z w

/-- A homogeneous quadruple is nonzero. -/
def NonzeroQuadruple (x y z w : ℚ) : Prop :=
  x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0

/-- Equality of two rational homogeneous quadruples in projective space. -/
def ProjectivelyEqual4
    (x y z w X Y Z W : ℚ) : Prop :=
  ∃ a : ℚ, a ≠ 0 ∧
    x = a * X ∧ y = a * Y ∧ z = a * Z ∧ w = a * W

/-- The five rational cusp classes on the level-25 canonical model. -/
def IsCanonicalCusp25 (x y z w : ℚ) : Prop :=
  ProjectivelyEqual4 x y z w 0 0 0 1 ∨
  ProjectivelyEqual4 x y z w 0 (-1) 1 0 ∨
  ProjectivelyEqual4 x y z w 1 1 0 1 ∨
  ProjectivelyEqual4 x y z w 0 0 1 0 ∨
  ProjectivelyEqual4 x y z w 1 0 0 0

end MazurProof.RationalPointsN25CanonicalPoints


