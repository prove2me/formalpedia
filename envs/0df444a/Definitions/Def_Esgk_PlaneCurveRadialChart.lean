-- Prove2me | Definitions.Def_Esgk_PlaneCurveRadialChart
-- name    : Esgk_PlaneCurveRadialChart
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:25.376548+00:00
-- url     : https://prove2.me/theorems/a4fedb3f-a7c8-452a-b9c3-0898632cb0a6
-- title:
--   Squared radius away from radial-critical points
-- statement:
--   This defines squared distance from a fixed center in Cartesian coordinates and the part of a polynomial curve on which its radial-critical polynomial does not vanish.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveRadialCritical
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_ChartBridge
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Filter Topology MvPolynomial
open PachDeZeeuw.Algebraic

namespace Esgk


def planeSquaredRadius (a : Point2) (z : ℝ × ℝ) : ℝ :=
  (z.1 - a 0) ^ 2 + (z.2 - a 1) ^ 2


def planeCurveRadialRegularLocus (G : PlanePoly) (a : Point2) : Set Point2 :=
  PlaneCurveZeroSet G \ PlaneCurveZeroSet (planeRadialCritical G a)


end Esgk


