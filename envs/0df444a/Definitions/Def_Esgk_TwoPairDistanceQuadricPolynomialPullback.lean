-- Prove2me | Definitions.Def_Esgk_TwoPairDistanceQuadricPolynomialPullback
-- name    : Esgk_TwoPairDistanceQuadricPolynomialPullback
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:51:48.720972+00:00
-- url     : https://prove2.me/theorems/ebb6b7ee-5ff1-491f-8c7c-f0a21845c265
-- title:
--   Polynomial equations pulled back through distance charts
-- statement:
--   This defines the numerators and denominator of the rational distance chart and the associated denominator-cleared polynomial pullbacks. Sums of squares combine the two curve equations, with an additional constraint in the exceptional chart.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlanePolynomialRationalPullback
import Definitions.Def_Esgk_TwoPairDistanceQuadricCharts
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open MvPolynomial

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartDenominator : PlanePoly := C 2 * X 1

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartFirstNumerator (a : ℝ) : PlanePoly := C (2 * a) * X 0 * X 1

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint (k : ℝ) : PlanePoly := C k * (X 0 ^ 2 - 1)

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartSecondNumerator (k : ℝ) : PlanePoly := X 1 ^ 2 + bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint k

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback (d : ℕ) (p : PlanePoly) (a k : ℝ) : PlanePoly :=
  planePolynomialRationalPullback d p (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartFirstNumerator a)
    (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartSecondNumerator k) bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartDenominator

def bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback (d : ℕ) (p : PlanePoly) (a b : ℝ) : PlanePoly :=
  planePolynomialRationalPullback d p (C a * X 0) (C b * X 1) 1

def distanceQuadricMainPolynomial (d : ℕ) (p q : PlanePoly) (u v : ℝ) : PlanePoly :=
  bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback d p v (u ^ 2 - v ^ 2) ^ 2 +
    bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback d q u (-(u ^ 2 - v ^ 2)) ^ 2

def distanceQuadricExceptionalPolynomial
    (d : ℕ) (p q : PlanePoly) (u v : ℝ) : PlanePoly :=
  bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint (u ^ 2 - v ^ 2) ^ 2 +
    (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback d p v 1 ^ 2 +
      bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback d q u (-1) ^ 2)


end Esgk


