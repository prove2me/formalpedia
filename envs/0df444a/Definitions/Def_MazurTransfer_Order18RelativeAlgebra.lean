-- Prove2me | Definitions.Def_MazurTransfer_Order18RelativeAlgebra
-- name    : MazurTransfer_Order18RelativeAlgebra
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T17:46:45.216285+00:00
-- url     : https://prove2.me/theorems/aae610da-f796-41d7-8241-21d9ebd9d002
-- title:
--   Order-18 number-field data: relative-algebra
-- statement:
--   Over the separately constructed coefficient field $K$, these data specify
--   \[M=K[S]/(S^3-3S-10),\]
--   its distinguished generators, and the original explicit rational quadratic representatives used by the order-18 descent. At this stage $M$ is only the specified algebra; its field validity is proved separately. No norm identity, class-number, unit-rank, Selmer or torsion conclusion is encoded. Named downstream consumers: relative irreducibility, the compositum class-number certificate, and the global and local Selmer calculations.
-- source:
--   Exact whole pure-data commands from user MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Original types, values and docstrings retained. Apache-2.0 attribution retained. Constructor validity, where needed, comes only from separately proved public irreducibility statements; no class-number, unit-rank, Selmer or torsion assertion is included.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_MazurTransfer_Order18CoefficientFields

noncomputable section
open Polynomial

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic.Q

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

abbrev tau := MazurTorsion.XOneEighteenRealCubicQuotient.tau

abbrev cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial

end MazurTorsion.XOneEighteenTwoDivisionArithmetic.Q

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

/-- The integral scaled abscissa of a nonzero two-torsion point. -/
def twoDivisionZ : F :=
  3 * sigma ^ 2 - 6 * sigma - 5

/-- The base-changed two-division polynomial over the real cubic field. -/
def relativePolynomial : Polynomial Q.K :=
  X ^ 3 - 3 * X - 10

/-- The relative cubic two-division algebra `K[S]/(S³-3S-10)`.

It is not declared to be a field in this module: that conclusion requires
the independent primitive-element/linear-disjointness certificate. -/
abbrev M := AdjoinRoot relativePolynomial

/-- The relative generator. -/
def s : M :=
  AdjoinRoot.root relativePolynomial

/-- The image of the real-cubic generator in the relative algebra. -/
def t : M :=
  algebraMap Q.K M Q.tau

/-- Scaled completed two-division coordinate in the relative algebra. -/
def relativeTwoDivisionZ : M :=
  3 * s ^ 2 - 6 * s - 5

/-- The canonical quadratic representative in the monogenic relative
cubic algebra. -/
def quadraticElement (a b c : Q.K) : M :=
  AdjoinRoot.mk relativePolynomial
    (C a * X ^ 2 + C b * X + C c)

/-- A generator above the first dyadic prime of the compositum. -/
def alpha : M :=
  quadraticElement
    ((2 * Q.tau ^ 2 - Q.tau - 1) / 18)
    ((-4 * Q.tau ^ 2 - Q.tau + 11) / 18)
    ((-4 * Q.tau ^ 2 + 2 * Q.tau + 14) / 18)

/-- A generator above the second dyadic prime of the compositum. -/
def beta : M :=
  quadraticElement
    ((-Q.tau ^ 2 + 2 * Q.tau + 2) / 18)
    ((-Q.tau ^ 2 + 2 * Q.tau + 8) / 18)
    ((8 * Q.tau ^ 2 + 8 * Q.tau - 10) / 18)

/-- A generator above the prime over `3`. -/
def rho : M :=
  quadraticElement (-Q.tau / 6) ((Q.tau - 2) / 6)
    ((2 * Q.tau ^ 2 + 2 * Q.tau - 8) / 6)

/-- First norm-one squareclass generator. -/
def h1 : M :=
  quadraticElement
    ((-Q.tau ^ 2 + 2 * Q.tau + 2) / 18)
    ((-Q.tau ^ 2 + 2 * Q.tau + 8) / 18)
    ((4 * Q.tau ^ 2 - 5 * Q.tau - 5) / 9)

/-- Second norm-one squareclass generator. -/
def h2 : M :=
  quadraticElement (1 / 6) (1 / 6)
    ((Q.tau ^ 2 + Q.tau) / 3 - 1)

/-- First generator of relative norm `4`. -/
def h3 : M :=
  quadraticElement
    ((2 * Q.tau ^ 2 - Q.tau + 2) / 18)
    ((2 * Q.tau ^ 2 - 7 * Q.tau + 14) / 18)
    ((4 * Q.tau ^ 2 - 5 * Q.tau + 4) / 9)

/-- Second generator whose norm is an explicit square in `K`. -/
def h4 : M :=
  quadraticElement ((-Q.tau ^ 2 + 3) / 6)
    ((Q.tau ^ 2 + 1) / 6) (Q.tau ^ 2 - 5 / 3)

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


