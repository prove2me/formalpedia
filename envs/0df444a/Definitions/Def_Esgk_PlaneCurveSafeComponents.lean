-- Prove2me | Definitions.Def_Esgk_PlaneCurveSafeComponents
-- name    : Esgk_PlaneCurveSafeComponents
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:52:39.661244+00:00
-- url     : https://prove2.me/theorems/8daecfb8-8c50-4c89-9541-4f975f97bed8
-- title:
--   Curve regions defined by gradient and radial conditions
-- statement:
--   This defines the regular curve region where the squared gradient exceeds a given level and the radial-critical polynomial is nonzero. It also defines the possible boundary locus where the gradient reaches the level or the radial-critical polynomial vanishes.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_FiniteBoundaryCurveComponents
import Definitions.Def_Esgk_PlaneCurveGradientCutoff
import Definitions.Def_Esgk_PlaneCurveRadialCritical
import Definitions.Def_Esgk_PlaneCurveRegularChart
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
def planeCurveSafeSet (G : PlanePoly) (ε : ℝ) (a : Point2) :
    Set (planeCurveRegularLocus G) :=
  {p | ε < MvPolynomial.eval (fun i ↦ (p : Point2) i) (planeGradientSquare G) ∧
    (p : Point2) ∉ PlaneCurveZeroSet (planeRadialCritical G a)}

 
def planeCurveSafeBoundary (G : PlanePoly) (ε : ℝ) (a : Point2) :
    Set (planeCurveRegularLocus G) :=
  {p | MvPolynomial.eval (fun i ↦ (p : Point2) i) (planeGradientSquare G) = ε ∨
    (p : Point2) ∈ PlaneCurveZeroSet (planeRadialCritical G a)}


end Esgk


