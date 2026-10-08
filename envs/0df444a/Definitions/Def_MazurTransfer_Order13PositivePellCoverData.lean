-- Prove2me | Definitions.Def_MazurTransfer_Order13PositivePellCoverData
-- name    : MazurTransfer_Order13PositivePellCoverData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T18:47:15.678429+00:00
-- url     : https://prove2.me/theorems/4f768099-c305-49ad-952a-85d05ee17a8e
-- title:
--   Order13: the fixed homogeneous sextic and Pell polynomial cover data
-- statement:
--   Define the integer homogeneous forms $F(a,b)$, $H(a,b)$ and $K(a,b)$ of degrees $6$, $19$ and $16$, and the two expressions $P(a,b,c)=H(a,b)+cK(a,b)$ and $N(a,b,c)=cK(a,b)-H(a,b)$. Their coefficients are given exactly in the definition file. These five polynomial definitions provide the data for the primitive positive Pell power-split arithmetic problem. This package asserts no arithmetic theorem, existence witness, point classification or rank computation.
-- source:
--   Five original pure integer-polynomial definitions from user MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, XOneThirteenPositivePell. Whole Lean AST commands and exact typed dependency graph identify the five definitions; original Apache-2.0 headers and authorship are retained. Named downstream consumers: MazurTransfer.order13_positive_pell_power_split_obstruction and the unchanged MazurTransfer.order13_no_noncuspidal_genus_two_point. No arithmetic assertion is packaged as a definition witness.

import Mathlib
noncomputable section


/- Source module: MazurTorsion.NumberTheory.XOneThirteenPositivePell. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Integral Pell allocation for the positive `X₁(13)` split system

The normalized cyclic-cubic descent in `XOneThirteenDescent` leaves one
positive system.  This file carries that system back to an integral point on
the homogeneous order-thirteen sextic.  The odd conic parameters give the
canonical positive ordinate `c=(m²+n²)/2`, and the two split coefficient
identities prove the sextic equation without introducing a new hypothesis.

Homogenizing the checked degree-`19` polynomial Pell certificate then gives

`(H+cK)(cK-H)=4b³⁸`.

Both factors are positive.  Moreover, primitivity of `(a,b)` shows that no
odd prime can divide both factors, so every odd prime in the denominator is
allocated to exactly one factor.  This is the arithmetic input needed to
continue from the Pell certificate to a power/divisor-class descent.

The final allocated-factor obstruction below is still a boundary, not a
rational-point classification or a Jacobian rank computation.  It has a
checked exact-order-thirteen consumer.
-/

namespace MazurTorsion.XOneThirteenDescent

open scoped WeierstrassCurve.Affine

/-- The degree-six integral homogenization of the order-thirteen sextic. -/
def integerSexticHomogeneous (a b : ℤ) : ℤ :=
  a ^ 6 + 2 * a ^ 5 * b + a ^ 4 * b ^ 2 +
    2 * a ^ 3 * b ^ 3 + 6 * a ^ 2 * b ^ 4 +
    4 * a * b ^ 5 + b ^ 6















/-- Degree-`19` integral homogenization of the Pell numerator. -/
def pellHHomogeneous (a b : ℤ) : ℤ :=
  a ^ 19 + 3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
    5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
    22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
    54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
    20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
    113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
    13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
    26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 +
    12 * a ^ 2 * b ^ 17 + 4 * a * b ^ 18

/-- Degree-`16` integral homogenization of the Pell denominator. -/
def pellKHomogeneous (a b : ℤ) : ℤ :=
  a ^ 16 + 2 * a ^ 15 * b + 4 * a ^ 13 * b ^ 3 +
    14 * a ^ 12 * b ^ 4 + 4 * a ^ 11 * b ^ 5 +
    2 * a ^ 10 * b ^ 6 + 32 * a ^ 9 * b ^ 7 +
    18 * a ^ 8 * b ^ 8 - 8 * a ^ 7 * b ^ 9 +
    29 * a ^ 6 * b ^ 10 + 24 * a ^ 5 * b ^ 11 -
    10 * a ^ 4 * b ^ 12 + 10 * a ^ 3 * b ^ 13 +
    10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 + 2 * b ^ 16















/-- The positive homogeneous Pell factor `H+cK`. -/
def positivePellFactor (a b c : ℤ) : ℤ :=
  pellHHomogeneous a b + c * pellKHomogeneous a b

/-- The positive magnitude `cK-H` of the negative conjugate factor. -/
def negativePellFactorMagnitude (a b c : ℤ) : ℤ :=
  c * pellKHomogeneous a b - pellHHomogeneous a b

















end MazurTorsion.XOneThirteenDescent

end

#print axioms MazurTorsion.XOneThirteenDescent.integerSexticHomogeneous
#print axioms MazurTorsion.XOneThirteenDescent.pellHHomogeneous
#print axioms MazurTorsion.XOneThirteenDescent.pellKHomogeneous
#print axioms MazurTorsion.XOneThirteenDescent.positivePellFactor
#print axioms MazurTorsion.XOneThirteenDescent.negativePellFactorMagnitude


