-- Prove2me | Definitions.Def_Esgk_AffineLinePolynomialRestriction
-- name    : Esgk_AffineLinePolynomialRestriction
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:54:39.157991+00:00
-- url     : https://prove2.me/theorems/8f77a32a-3a6b-4c65-91a1-7a8722477d54
-- title:
--   Restricting a plane polynomial to an affine line
-- statement:
--   This parametrizes the line through a point in a chosen direction and forms the one-variable polynomial obtained by restricting a bivariate polynomial to that line.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CircleRationalParametrization
import Definitions.Def_Esgk_PlaneAffineLinePolynomial
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic Polynomial

 
def affineLineParam (x v : Point2) (t : ℝ) : Point2 :=
  x + t • v


def bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial (x v : Point2) (i : Fin 2) : Polynomial ℝ :=
  C (x i) + C (v i) * X


def bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial
    (x v : Point2) (i j : ℕ) (a : ℝ) : Polynomial ℝ :=
  C a * bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 0 ^ i *
    bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 1 ^ j


def affineLinePolynomialRestriction (p : PlanePoly) (x v : Point2) : Polynomial ℝ :=
  (AddMonoidAlgebra.coeff p).sum fun exponent coefficient ↦
    bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial x v (exponent 0) (exponent 1) coefficient


end Esgk


