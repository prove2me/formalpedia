-- Prove2me | Definitions.Def_RationalPointsN25CanonicalSourceBridge
-- name    : RationalPointsN25CanonicalSourceBridge
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:49.493282+00:00
-- url     : https://prove2.me/theorems/7f7304da-4e98-414b-bcee-be6094899707
-- title:
--   Adjoint map from Sutherland’s model to the canonical quotient
-- statement:
--   The file defines four degree-nine adjoint coordinates giving a polynomial map from Sutherland’s optimized affine model of $X_1(25)$ to the canonical complete intersection. It also defines the base-point resultant polynomial and extensive Bézout coefficients certifying nonvanishing of the homogeneous image and controlling the third coordinate. This is an explicit certificate package for carrying primitive Tate solutions to noncuspidal canonical points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_RationalPointsN25QuotientAction
import Definitions.Def_RationalPointsN25SutherlandBridge
import Definitions.Def_TateOrder25Factor
/-!
# Canonical quotient map from Sutherland's level-25 source model

This file gives an explicit polynomial map from Sutherland's optimized affine
model of `X₁(25)` to the stored genus-four canonical model of its diamond
quotient.  The map was recovered exactly from the degree-nine adjoint space of
the projective plane closure.  Pullback by the diamond involution `⟨7⟩` has a
four-dimensional invariant subspace; the residual diamond action identifies
that subspace with the order-five action already formalized on the canonical
model.

Only the resulting polynomial data enter the formal proof.  The quadric and
cubic pullbacks below are literal multiples of Sutherland's plane equation,
verified by `ring`.  Composing with the preceding Tate-to-Sutherland bridge
therefore gives a fully explicit map from every primitive order-25 Tate
solution to the canonical complete intersection.

The resultant certificates below also prove that the resulting homogeneous
vector is nonzero and is not one of the five canonical cusps.  The remaining
N25 obstruction is therefore the global rational-point classification on the
canonical quotient, not a comparison between models.
-/

namespace MazurProof.RationalPointsN25CanonicalSourceBridge

open RationalPointsN25CanonicalPoints
open RationalPointsN25QuotientAction
open RationalPointsN25SutherlandBridge
open TateOrder25Factor

/-! ## Polynomial canonical coordinates on the optimized affine source -/

/-- The degree-seven factor in the first canonical coordinate.  The full
coordinate is `-(y-1)²` times this adjoint polynomial. -/
def sutherlandCanonicalXCore25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 2 - 2 * x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4 - x ^ 5 * y +
    x ^ 4 * y ^ 2 + x ^ 3 * y ^ 3 - x ^ 2 * y ^ 4 + x ^ 4 * y -
    2 * x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3 - x ^ 2 * y ^ 2 + x * y ^ 3 +
    2 * x ^ 2 * y - 2 * x * y ^ 2 - 2 * x ^ 2 + 3 * x * y - y ^ 2 -
    2 * x + 2 * y - 1

/-- First homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalX25 (x y : ℚ) : ℚ :=
  -(y - 1) ^ 2 * sutherlandCanonicalXCore25 x y

/-- Second homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalY25 (x y : ℚ) : ℚ :=
  -(x ^ 5 * y ^ 4 - 2 * x ^ 4 * y ^ 5 + x ^ 3 * y ^ 6 + x ^ 6 * y ^ 2 -
    8 * x ^ 5 * y ^ 3 + 13 * x ^ 4 * y ^ 4 - 6 * x ^ 3 * y ^ 5 +
    6 * x ^ 5 * y ^ 2 - 10 * x ^ 4 * y ^ 3 + 2 * x ^ 3 * y ^ 4 +
    2 * x ^ 2 * y ^ 5 - 2 * x ^ 5 * y + 4 * x ^ 4 * y ^ 2 -
    5 * x ^ 3 * y ^ 3 + 4 * x ^ 2 * y ^ 4 - x * y ^ 5 - 2 * x ^ 4 * y +
    12 * x ^ 3 * y ^ 2 - 10 * x ^ 2 * y ^ 3 - 6 * x ^ 3 * y +
    3 * x ^ 2 * y ^ 2 + 3 * x * y ^ 3 + x ^ 3 + x ^ 2 * y -
    2 * x * y ^ 2 + y ^ 3 - 3 * y ^ 2 + 3 * y - 1)

/-- Third homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalZ25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 4 - 2 * x ^ 4 * y ^ 5 + x ^ 3 * y ^ 6 -
    5 * x ^ 5 * y ^ 3 + 10 * x ^ 4 * y ^ 4 - 5 * x ^ 3 * y ^ 5 +
    x ^ 6 * y + 3 * x ^ 5 * y ^ 2 - 8 * x ^ 4 * y ^ 3 +
    3 * x ^ 3 * y ^ 4 + x ^ 2 * y ^ 5 - 2 * x ^ 5 * y +
    4 * x ^ 4 * y ^ 2 - 4 * x ^ 3 * y ^ 3 + 2 * x ^ 2 * y ^ 4 +
    5 * x ^ 3 * y ^ 2 - 3 * x ^ 2 * y ^ 3 - 2 * x * y ^ 4 - x ^ 4 -
    2 * x ^ 3 * y + 3 * x * y ^ 3 + x ^ 3 - x ^ 2 * y + y ^ 3 +
    x ^ 2 - x * y - 3 * y ^ 2 + 3 * y - 1

/-- The degree-eight factor in the fourth canonical coordinate.  The full
coordinate is `(x-y+1)` times this adjoint polynomial. -/
def sutherlandCanonicalWCore25 (x y : ℚ) : ℚ :=
  x ^ 5 * y ^ 3 - 2 * x ^ 4 * y ^ 4 + x ^ 3 * y ^ 5 -
    2 * x ^ 5 * y ^ 2 + 3 * x ^ 4 * y ^ 3 - x ^ 2 * y ^ 5 + x ^ 5 * y -
    3 * x ^ 3 * y ^ 3 + 2 * x ^ 2 * y ^ 4 - 2 * x ^ 3 * y ^ 2 +
    2 * x ^ 2 * y ^ 3 + 3 * x ^ 3 * y - x ^ 2 * y ^ 2 -
    2 * x * y ^ 3 - x ^ 3 - x ^ 2 * y + 2 * x * y ^ 2 + y ^ 2 -
    2 * y + 1

/-- Fourth homogeneous coordinate of the canonical quotient map from
Sutherland's optimized affine source. -/
def sutherlandCanonicalW25 (x y : ℚ) : ℚ :=
  (x - y + 1) * sutherlandCanonicalWCore25 x y

/-- The four degree-nine adjoint coordinates packaged as a point in the
ambient canonical four-space. -/
def sutherlandCanonicalCoordinates25 (x y : ℚ) : Coordinates25 :=
  ⟨sutherlandCanonicalX25 x y, sutherlandCanonicalY25 x y,
    sutherlandCanonicalZ25 x y, sutherlandCanonicalW25 x y⟩

/-! ## Affine base-point exclusion -/

/-- The monic degree-ten factor in the resultant of the first and fourth
adjoint cores with respect to the source coordinate `x`. -/
def sutherlandBasePointFiber25 (y : ℚ) : ℚ :=
  y ^ 10 - 4 * y ^ 9 + 5 * y ^ 8 + 6 * y ^ 7 - 26 * y ^ 6 +
    24 * y ^ 5 + 15 * y ^ 4 - 50 * y ^ 3 + 45 * y ^ 2 - 20 * y + 5

/-- Integral polynomial underlying the base-point fibre obstruction. -/
noncomputable def sutherlandBasePointFiberPoly25 : Polynomial ℤ :=
  Polynomial.X ^ 10 - 4 * Polynomial.X ^ 9 + 5 * Polynomial.X ^ 8 +
    6 * Polynomial.X ^ 7 - 26 * Polynomial.X ^ 6 + 24 * Polynomial.X ^ 5 +
    15 * Polynomial.X ^ 4 - 50 * Polynomial.X ^ 3 + 45 * Polynomial.X ^ 2 -
    20 * Polynomial.X + 5

/-- Bezout coefficient multiplying the first adjoint core in the exact
base-point resultant identity. -/
def sutherlandBasePointBezoutX25 (x y : ℚ) : ℚ :=
  -x ^ 4 * y ^ 17 + 13 * x ^ 4 * y ^ 16 - 74 * x ^ 4 * y ^ 15 +
    236 * x ^ 4 * y ^ 14 - 427 * x ^ 4 * y ^ 13 +
    294 * x ^ 4 * y ^ 12 + 508 * x ^ 4 * y ^ 11 -
    1514 * x ^ 4 * y ^ 10 + 1413 * x ^ 4 * y ^ 9 +
    300 * x ^ 4 * y ^ 8 - 2214 * x ^ 4 * y ^ 7 +
    2699 * x ^ 4 * y ^ 6 - 1853 * x ^ 4 * y ^ 5 +
    812 * x ^ 4 * y ^ 4 - 224 * x ^ 4 * y ^ 3 + 34 * x ^ 4 * y ^ 2 -
    2 * x ^ 4 * y + x ^ 3 * y ^ 18 - 12 * x ^ 3 * y ^ 17 +
    61 * x ^ 3 * y ^ 16 - 165 * x ^ 3 * y ^ 15 +
    223 * x ^ 3 * y ^ 14 - 20 * x ^ 3 * y ^ 13 -
    388 * x ^ 3 * y ^ 12 + 365 * x ^ 3 * y ^ 11 +
    480 * x ^ 3 * y ^ 10 - 1137 * x ^ 3 * y ^ 9 +
    416 * x ^ 3 * y ^ 8 + 891 * x ^ 3 * y ^ 7 -
    1271 * x ^ 3 * y ^ 6 + 770 * x ^ 3 * y ^ 5 -
    239 * x ^ 3 * y ^ 4 + 18 * x ^ 3 * y ^ 3 + 10 * x ^ 3 * y ^ 2 -
    2 * x ^ 3 * y - x ^ 2 * y ^ 18 + 13 * x ^ 2 * y ^ 17 -
    70 * x ^ 2 * y ^ 16 + 193 * x ^ 2 * y ^ 15 -
    223 * x ^ 2 * y ^ 14 - 237 * x ^ 2 * y ^ 13 +
    1219 * x ^ 2 * y ^ 12 - 1549 * x ^ 2 * y ^ 11 -
    188 * x ^ 2 * y ^ 10 + 2833 * x ^ 2 * y ^ 9 -
    3029 * x ^ 2 * y ^ 8 + 112 * x ^ 2 * y ^ 7 +
    2756 * x ^ 2 * y ^ 6 - 3265 * x ^ 2 * y ^ 5 +
    2098 * x ^ 2 * y ^ 4 - 855 * x ^ 2 * y ^ 3 +
    222 * x ^ 2 * y ^ 2 - 33 * x ^ 2 * y + 2 * x ^ 2 -
    3 * x * y ^ 16 + 34 * x * y ^ 15 - 168 * x * y ^ 14 +
    458 * x * y ^ 13 - 660 * x * y ^ 12 + 136 * x * y ^ 11 +
    1350 * x * y ^ 10 - 2502 * x * y ^ 9 + 1479 * x * y ^ 8 +
    1182 * x * y ^ 7 - 2814 * x * y ^ 6 + 2353 * x * y ^ 5 -
    1091 * x * y ^ 4 + 264 * x * y ^ 3 - 7 * x * y ^ 2 -
    12 * x * y + 2 * x - 4 * y ^ 14 + 38 * y ^ 13 - 163 * y ^ 12 +
    397 * y ^ 11 - 548 * y ^ 10 + 283 * y ^ 9 + 316 * y ^ 8 -
    519 * y ^ 7 - 62 * y ^ 6 + 752 * y ^ 5 - 850 * y ^ 4 +
    511 * y ^ 3 - 185 * y ^ 2 + 37 * y - 3

/-- Bezout coefficient multiplying the fourth adjoint core in the exact
base-point resultant identity. -/
def sutherlandBasePointBezoutW25 (x y : ℚ) : ℚ :=
  x ^ 4 * y ^ 16 - 12 * x ^ 4 * y ^ 15 + 62 * x ^ 4 * y ^ 14 -
    174 * x ^ 4 * y ^ 13 + 253 * x ^ 4 * y ^ 12 -
    41 * x ^ 4 * y ^ 11 - 549 * x ^ 4 * y ^ 10 +
    965 * x ^ 4 * y ^ 9 - 448 * x ^ 4 * y ^ 8 -
    748 * x ^ 4 * y ^ 7 + 1466 * x ^ 4 * y ^ 6 -
    1233 * x ^ 4 * y ^ 5 + 620 * x ^ 4 * y ^ 4 -
    192 * x ^ 4 * y ^ 3 + 32 * x ^ 4 * y ^ 2 - 2 * x ^ 4 * y -
    x ^ 3 * y ^ 17 + 11 * x ^ 3 * y ^ 16 - 50 * x ^ 3 * y ^ 15 +
    114 * x ^ 3 * y ^ 14 - 98 * x ^ 3 * y ^ 13 -
    129 * x ^ 3 * y ^ 12 + 382 * x ^ 3 * y ^ 11 -
    113 * x ^ 3 * y ^ 10 - 682 * x ^ 3 * y ^ 9 +
    915 * x ^ 3 * y ^ 8 - 6 * x ^ 3 * y ^ 7 - 954 * x ^ 3 * y ^ 6 +
    1008 * x ^ 3 * y ^ 5 - 537 * x ^ 3 * y ^ 4 +
    160 * x ^ 3 * y ^ 3 - 20 * x ^ 3 * y ^ 2 + x ^ 2 * y ^ 17 -
    12 * x ^ 2 * y ^ 16 + 61 * x ^ 2 * y ^ 15 -
    168 * x ^ 2 * y ^ 14 + 242 * x ^ 2 * y ^ 13 -
    56 * x ^ 2 * y ^ 12 - 448 * x ^ 2 * y ^ 11 +
    789 * x ^ 2 * y ^ 10 - 398 * x ^ 2 * y ^ 9 -
    408 * x ^ 2 * y ^ 8 + 821 * x ^ 2 * y ^ 7 -
    745 * x ^ 2 * y ^ 6 + 527 * x ^ 2 * y ^ 5 -
    304 * x ^ 2 * y ^ 4 + 132 * x ^ 2 * y ^ 3 -
    39 * x ^ 2 * y ^ 2 + 5 * x ^ 2 * y - x * y ^ 16 +
    14 * x * y ^ 15 - 84 * x * y ^ 14 + 287 * x * y ^ 13 -
    595 * x * y ^ 12 + 662 * x * y ^ 11 + 25 * x * y ^ 10 -
    1332 * x * y ^ 9 + 2018 * x * y ^ 8 - 990 * x * y ^ 7 -
    1046 * x * y ^ 6 + 2267 * x * y ^ 5 - 1970 * x * y ^ 4 +
    1021 * x * y ^ 3 - 330 * x * y ^ 2 + 59 * x * y - 4 * x +
    y ^ 15 - 13 * y ^ 14 + 73 * y ^ 13 - 232 * y ^ 12 +
    436 * y ^ 11 - 405 * y ^ 10 - 113 * y ^ 9 + 716 * y ^ 8 -
    450 * y ^ 7 - 811 * y ^ 6 + 1858 * y ^ 5 - 1790 * y ^ 4 +
    1036 * y ^ 3 - 380 * y ^ 2 + 82 * y - 8

/-! ## Exclusion of the remaining cusp fibres -/

def sutherlandCanonicalZBezoutSource25CoefficientFive (y : ℚ) : ℚ :=
  -y * (2 * y ^ 16 - 25 * y ^ 15 + 136 * y ^ 14 - 404 * y ^ 13 + 616 * y ^ 12 - 18 * y ^ 11 - 1983 * y ^ 10 + 4202 * y ^ 9 - 3847 * y ^ 8 + 72 * y ^ 7 + 3907 * y ^ 6 - 4759 * y ^ 5 + 3073 * y ^ 4 - 1232 * y ^ 3 + 285 * y ^ 2 - 31 * y - 1)

def sutherlandCanonicalZBezoutSource25CoefficientFour (y : ℚ) : ℚ :=
  -y * (2 * y ^ 19 - 35 * y ^ 18 + 269 * y ^ 17 - 1188 * y ^ 16 + 3230 * y ^ 15 - 4983 * y ^ 14 + 1348 * y ^ 13 + 12952 * y ^ 12 - 33089 * y ^ 11 + 40446 * y ^ 10 - 19906 * y ^ 9 - 18344 * y ^ 8 + 46190 * y ^ 7 - 47684 * y ^ 6 + 31198 * y ^ 5 - 13822 * y ^ 4 + 4090 * y ^ 3 - 705 * y ^ 2 + 46 * y + 6)

def sutherlandCanonicalZBezoutSource25CoefficientThree (y : ℚ) : ℚ :=
  2 * y ^ 21 - 35 * y ^ 20 + 269 * y ^ 19 - 1191 * y ^ 18 + 3276 * y ^ 17 - 5291 * y ^ 16 + 2526 * y ^ 15 + 10236 * y ^ 14 - 29941 * y ^ 13 + 42264 * y ^ 12 - 35382 * y ^ 11 + 15428 * y ^ 10 + 809 * y ^ 9 - 5045 * y ^ 8 + 1322 * y ^ 7 + 2854 * y ^ 6 - 3719 * y ^ 5 + 2359 * y ^ 4 - 903 * y ^ 3 + 201 * y ^ 2 - 17 * y - 1

def sutherlandCanonicalZBezoutSource25CoefficientTwo (y : ℚ) : ℚ :=
  2 * y ^ 20 - 19 * y ^ 19 + 46 * y ^ 18 + 195 * y ^ 17 - 1695 * y ^ 16 + 5490 * y ^ 15 - 9269 * y ^ 14 + 4574 * y ^ 13 + 16470 * y ^ 12 - 46123 * y ^ 11 + 60164 * y ^ 10 - 43439 * y ^ 9 + 9542 * y ^ 8 + 15860 * y ^ 7 - 21757 * y ^ 6 + 14910 * y ^ 5 - 6519 * y ^ 4 + 1821 * y ^ 3 - 265 * y ^ 2 + 5

def sutherlandCanonicalZBezoutSource25CoefficientOne (y : ℚ) : ℚ :=
  -(y - 1) * (4 * y ^ 18 - 54 * y ^ 17 + 309 * y ^ 16 - 940 * y ^ 15 + 1364 * y ^ 14 + 616 * y ^ 13 - 7025 * y ^ 12 + 14549 * y ^ 11 - 13651 * y ^ 10 - 470 * y ^ 9 + 17498 * y ^ 8 - 22520 * y ^ 7 + 14675 * y ^ 6 - 4673 * y ^ 5 - 383 * y ^ 4 + 1080 * y ^ 3 - 490 * y ^ 2 + 106 * y - 9)

def sutherlandCanonicalZBezoutSource25CoefficientZero (y : ℚ) : ℚ :=
  (y - 1) ^ 2 * (2 * y ^ 16 - 32 * y ^ 15 + 209 * y ^ 14 - 754 * y ^ 13 + 1595 * y ^ 12 - 1618 * y ^ 11 - 1015 * y ^ 10 + 6265 * y ^ 9 - 10257 * y ^ 8 + 8795 * y ^ 7 - 3143 * y ^ 6 - 1426 * y ^ 5 + 2440 * y ^ 4 - 1480 * y ^ 3 + 498 * y ^ 2 - 92 * y + 6)

/-- Bezout coefficient multiplying Sutherland's source equation in the exact
resultant certificate for the third canonical coordinate.  Its explicit form
keeps the nonvanishing argument reducible to kernel-checked ring arithmetic. -/
def sutherlandCanonicalZBezoutSource25 (x y : ℚ) : ℚ :=
  x ^ 5 * sutherlandCanonicalZBezoutSource25CoefficientFive y +
    x ^ 4 * sutherlandCanonicalZBezoutSource25CoefficientFour y +
    x ^ 3 * sutherlandCanonicalZBezoutSource25CoefficientThree y +
    x ^ 2 * sutherlandCanonicalZBezoutSource25CoefficientTwo y +
    x ^ 1 * sutherlandCanonicalZBezoutSource25CoefficientOne y +
    x ^ 0 * sutherlandCanonicalZBezoutSource25CoefficientZero y

def sutherlandCanonicalZBezoutCoordinate25CoefficientSeven (y : ℚ) : ℚ :=
  y ^ 2 * (2 * y ^ 16 - 25 * y ^ 15 + 136 * y ^ 14 - 404 * y ^ 13 + 616 * y ^ 12 - 18 * y ^ 11 - 1983 * y ^ 10 + 4202 * y ^ 9 - 3847 * y ^ 8 + 72 * y ^ 7 + 3907 * y ^ 6 - 4759 * y ^ 5 + 3073 * y ^ 4 - 1232 * y ^ 3 + 285 * y ^ 2 - 31 * y - 1)

def sutherlandCanonicalZBezoutCoordinate25CoefficientSix (y : ℚ) : ℚ :=
  y ^ 2 * (2 * y ^ 19 - 33 * y ^ 18 + 238 * y ^ 17 - 975 * y ^ 16 + 2393 * y ^ 15 - 3019 * y ^ 14 - 922 * y ^ 13 + 11639 * y ^ 12 - 22956 * y ^ 11 + 22010 * y ^ 10 - 4091 * y ^ 9 - 18500 * y ^ 8 + 29782 * y ^ 7 - 26427 * y ^ 6 + 15988 * y ^ 5 - 6768 * y ^ 4 + 1972 * y ^ 3 - 328 * y ^ 2 + 18 * y + 5)

def sutherlandCanonicalZBezoutCoordinate25CoefficientFive (y : ℚ) : ℚ :=
  -y * (4 * y ^ 21 - 64 * y ^ 20 + 449 * y ^ 19 - 1786 * y ^ 18 + 4210 * y ^ 17 - 4829 * y ^ 16 - 3013 * y ^ 15 + 22034 * y ^ 14 - 39445 * y ^ 13 + 33219 * y ^ 12 - 840 * y ^ 11 - 29562 * y ^ 10 + 31574 * y ^ 9 - 9908 * y ^ 8 - 12809 * y ^ 7 + 21442 * y ^ 6 - 16810 * y ^ 5 + 8478 * y ^ 4 - 2819 * y ^ 3 + 569 * y ^ 2 - 50 * y - 2)

def sutherlandCanonicalZBezoutCoordinate25CoefficientFour (y : ℚ) : ℚ :=
  y * (2 * y ^ 22 - 29 * y ^ 21 + 176 * y ^ 20 - 550 * y ^ 19 + 737 * y ^ 18 + 780 * y ^ 17 - 4947 * y ^ 16 + 7765 * y ^ 15 - 1073 * y ^ 14 - 14532 * y ^ 13 + 21162 * y ^ 12 - 3848 * y ^ 11 - 23818 * y ^ 10 + 36407 * y ^ 9 - 30142 * y ^ 8 + 17699 * y ^ 7 - 7846 * y ^ 6 + 2762 * y ^ 5 - 874 * y ^ 4 + 291 * y ^ 3 - 126 * y ^ 2 + 40 * y - 8)

def sutherlandCanonicalZBezoutCoordinate25CoefficientThree (y : ℚ) : ℚ :=
  -2 * y ^ 23 + 33 * y ^ 22 - 238 * y ^ 21 + 987 * y ^ 20 - 2576 * y ^ 19 + 4242 * y ^ 18 - 3742 * y ^ 17 - 996 * y ^ 16 + 11045 * y ^ 15 - 29847 * y ^ 14 + 61011 * y ^ 13 - 90591 * y ^ 12 + 82644 * y ^ 11 - 21741 * y ^ 10 - 52029 * y ^ 9 + 86168 * y ^ 8 - 73762 * y ^ 7 + 43137 * y ^ 6 - 18533 * y ^ 5 + 6012 * y ^ 4 - 1445 * y ^ 3 + 234 * y ^ 2 - 17 * y - 1

def sutherlandCanonicalZBezoutCoordinate25CoefficientTwo (y : ℚ) : ℚ :=
  (y - 1) * (2 * y ^ 21 - 41 * y ^ 20 + 349 * y ^ 19 - 1660 * y ^ 18 + 4843 * y ^ 17 - 8406 * y ^ 16 + 5501 * y ^ 15 + 12222 * y ^ 14 - 41645 * y ^ 13 + 63218 * y ^ 12 - 60327 * y ^ 11 + 39367 * y ^ 10 - 16736 * y ^ 9 - 1966 * y ^ 8 + 15180 * y ^ 7 - 18584 * y ^ 6 + 13569 * y ^ 5 - 6614 * y ^ 4 + 2146 * y ^ 3 - 446 * y ^ 2 + 52 * y - 3)

def sutherlandCanonicalZBezoutCoordinate25CoefficientOne (y : ℚ) : ℚ :=
  (y - 1) ^ 2 * (10 * y ^ 18 - 141 * y ^ 17 + 871 * y ^ 16 - 3062 * y ^ 15 + 6383 * y ^ 14 - 6248 * y ^ 13 - 5198 * y ^ 12 + 28544 * y ^ 11 - 47576 * y ^ 10 + 41932 * y ^ 9 - 13743 * y ^ 8 - 12528 * y ^ 7 + 20148 * y ^ 6 - 13914 * y ^ 5 + 5773 * y ^ 4 - 1440 * y ^ 3 + 164 * y ^ 2 + 7 * y - 3)

def sutherlandCanonicalZBezoutCoordinate25CoefficientZero (y : ℚ) : ℚ :=
  -(y - 1) ^ 3 * (y ^ 16 - 22 * y ^ 15 + 165 * y ^ 14 - 650 * y ^ 13 + 1487 * y ^ 12 - 1722 * y ^ 11 - 476 * y ^ 10 + 5469 * y ^ 9 - 9926 * y ^ 8 + 9613 * y ^ 7 - 4998 * y ^ 6 + 620 * y ^ 5 + 975 * y ^ 4 - 760 * y ^ 3 + 258 * y ^ 2 - 42 * y + 1)

/-- Bezout coefficient multiplying the third canonical coordinate in its
source-curve resultant certificate. -/
def sutherlandCanonicalZBezoutCoordinate25 (x y : ℚ) : ℚ :=
  x ^ 7 * sutherlandCanonicalZBezoutCoordinate25CoefficientSeven y +
    x ^ 6 * sutherlandCanonicalZBezoutCoordinate25CoefficientSix y +
    x ^ 5 * sutherlandCanonicalZBezoutCoordinate25CoefficientFive y +
    x ^ 4 * sutherlandCanonicalZBezoutCoordinate25CoefficientFour y +
    x ^ 3 * sutherlandCanonicalZBezoutCoordinate25CoefficientThree y +
    x ^ 2 * sutherlandCanonicalZBezoutCoordinate25CoefficientTwo y +
    x ^ 1 * sutherlandCanonicalZBezoutCoordinate25CoefficientOne y +
    x ^ 0 * sutherlandCanonicalZBezoutCoordinate25CoefficientZero y

/-! ## Exact pullback of the canonical equations -/

/-- Degree-six cofactor in the pullback of the canonical quadric. -/
def sutherlandCanonicalQuadricCofactor25 (x y : ℚ) : ℚ :=
  (x - 1) *
    (2 * x ^ 3 * y ^ 2 - 3 * x ^ 2 * y ^ 3 + x * y ^ 4 -
      3 * x ^ 3 * y + 5 * x ^ 2 * y ^ 2 - 2 * x * y ^ 3 + x ^ 3 -
      2 * x ^ 2 * y + x * y ^ 2 + x ^ 2 - 2 * x * y + y ^ 2 +
      2 * x - 2 * y + 1)

def sutherlandCanonicalCubicCofactor25CoefficientTen (y : ℚ) : ℚ :=
  -y ^ 2 * (y - 1) ^ 3

def sutherlandCanonicalCubicCofactor25CoefficientNine (y : ℚ) : ℚ :=
  y * (y - 1) * (3 * y - 2) * (2 * y ^ 3 - 3 * y ^ 2 + y - 1)

def sutherlandCanonicalCubicCofactor25CoefficientEight (y : ℚ) : ℚ :=
  -y * (13 * y ^ 6 - 35 * y ^ 5 + 20 * y ^ 4 + 12 * y ^ 3 - 15 * y ^ 2 + 7 * y - 1)

def sutherlandCanonicalCubicCofactor25CoefficientSeven (y : ℚ) : ℚ :=
  13 * y ^ 8 - 18 * y ^ 7 - 53 * y ^ 6 + 123 * y ^ 5 - 97 * y ^ 4 + 48 * y ^ 3 - 14 * y ^ 2 + 1

def sutherlandCanonicalCubicCofactor25CoefficientSix (y : ℚ) : ℚ :=
  -6 * y ^ 9 - 11 * y ^ 8 + 103 * y ^ 7 - 172 * y ^ 6 + 152 * y ^ 5 - 150 * y ^ 4 + 131 * y ^ 3 - 68 * y ^ 2 + 20 * y - 2

def sutherlandCanonicalCubicCofactor25CoefficientFive (y : ℚ) : ℚ :=
  y ^ 10 + 13 * y ^ 9 - 58 * y ^ 8 + 85 * y ^ 7 - 112 * y ^ 6 + 208 * y ^ 5 - 237 * y ^ 4 + 152 * y ^ 3 - 71 * y ^ 2 + 24 * y - 4

def sutherlandCanonicalCubicCofactor25CoefficientFour (y : ℚ) : ℚ :=
  -(y - 1) * (3 * y ^ 9 - 5 * y ^ 8 + 4 * y ^ 7 - 33 * y ^ 6 + 68 * y ^ 5 - 42 * y ^ 4 + 36 * y ^ 3 - 41 * y ^ 2 + 20 * y - 5)

def sutherlandCanonicalCubicCofactor25CoefficientThree (y : ℚ) : ℚ :=
  (y - 1) ^ 2 * (y ^ 8 - y ^ 6 - 8 * y ^ 5 + 19 * y ^ 4 - y ^ 3 + 6 * y ^ 2 - 7 * y + 1)

def sutherlandCanonicalCubicCofactor25CoefficientTwo (y : ℚ) : ℚ :=
  -(y - 1) ^ 3 * (2 * y ^ 6 - 4 * y ^ 5 + 9 * y ^ 4 - 11 * y ^ 3 + 20 * y ^ 2 - 10 * y + 4)

def sutherlandCanonicalCubicCofactor25CoefficientOne (y : ℚ) : ℚ :=
  (y - 1) ^ 4 * (y ^ 2 - y + 1) * (2 * y ^ 2 - y + 4)

def sutherlandCanonicalCubicCofactor25CoefficientZero (y : ℚ) : ℚ :=
  -(y - 1) ^ 5 * (y ^ 2 - y + 1)

/-- Degree-fifteen cofactor in the pullback of the canonical cubic.  Keeping
this literal polynomial makes the model comparison independently checkable by
the kernel rather than relying on the external adjoint-space computation. -/
def sutherlandCanonicalCubicCofactor25 (x y : ℚ) : ℚ :=
  x ^ 10 * sutherlandCanonicalCubicCofactor25CoefficientTen y +
    x ^ 9 * sutherlandCanonicalCubicCofactor25CoefficientNine y +
    x ^ 8 * sutherlandCanonicalCubicCofactor25CoefficientEight y +
    x ^ 7 * sutherlandCanonicalCubicCofactor25CoefficientSeven y +
    x ^ 6 * sutherlandCanonicalCubicCofactor25CoefficientSix y +
    x ^ 5 * sutherlandCanonicalCubicCofactor25CoefficientFive y +
    x ^ 4 * sutherlandCanonicalCubicCofactor25CoefficientFour y +
    x ^ 3 * sutherlandCanonicalCubicCofactor25CoefficientThree y +
    x ^ 2 * sutherlandCanonicalCubicCofactor25CoefficientTwo y +
    x ^ 1 * sutherlandCanonicalCubicCofactor25CoefficientOne y +
    x ^ 0 * sutherlandCanonicalCubicCofactor25CoefficientZero y

/-! ## Composition with the primitive Tate locus -/

/-- The optimized Sutherland `x` coordinate attached to a Tate pair. -/
def tateSutherlandXCoordinate25 (b c : ℚ) : ℚ :=
  tateToSutherlandXNum25 b c / tateToSutherlandCommon25 b c

/-- The optimized Sutherland `y` coordinate attached to a Tate pair. -/
def tateSutherlandYCoordinate25 (b c : ℚ) : ℚ :=
  tateToSutherlandCommon25 b c * (b - c) /
    tateToSutherlandYDen25 b c

/-- The canonical quotient coordinates evaluated at the explicit optimized
Sutherland coordinates of a Tate pair `(b,c)`. -/
def tateCanonicalCoordinates25 (b c : ℚ) : Coordinates25 :=
  sutherlandCanonicalCoordinates25
    (tateSutherlandXCoordinate25 b c)
    (tateSutherlandYCoordinate25 b c)

end MazurProof.RationalPointsN25CanonicalSourceBridge


