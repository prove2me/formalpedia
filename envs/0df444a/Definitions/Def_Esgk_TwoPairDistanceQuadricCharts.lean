-- Prove2me | Definitions.Def_Esgk_TwoPairDistanceQuadricCharts
-- name    : Esgk_TwoPairDistanceQuadricCharts
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:47.262001+00:00
-- url     : https://prove2.me/theorems/d0c1b246-2362-4885-ac6e-a001c8dbba2c
-- title:
--   Coordinate maps for two distance constraints
-- statement:
--   This defines rational coordinate maps into pairs of planar points, using a shared horizontal parameter and a denominator twice the second parameter. A separate coordinate map describes the exceptional branch used with the distance quadric.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial

def bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (x y : ℝ) : Point2 := WithLp.toLp 2 ![x, y]

def bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK (u v : ℝ) : ℝ := u ^ 2 - v ^ 2

 
def distanceQuadricChart (u v : ℝ) (z : Point2) : Point2 × Point2 :=
  let t := z 0
  let s := z 1
  let k := bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK u v
  (bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (v * t) ((s ^ 2 + k * (t ^ 2 - 1)) / (2 * s)),
    bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (u * t) ((s ^ 2 - k * (t ^ 2 - 1)) / (2 * s)))

 
def distanceQuadricExceptionalChart (u v : ℝ) (z : Point2) : Point2 × Point2 :=
  (bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (v * z 0) (z 1), bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (u * z 0) (-(z 1)))


end Esgk


