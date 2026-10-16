-- Prove2me | Definitions.Def_Esgk_PlaneCurveExceptionalSample
-- name    : Esgk_PlaneCurveExceptionalSample
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:57.377196+00:00
-- url     : https://prove2.me/theorems/0634bb2c-b791-4576-bc92-e8aadfa5c512
-- title:
--   Singular and radial-critical sample points
-- statement:
--   This selects the points of a finite planar sample that are singular points of a given polynomial curve or radial-critical points relative to a fixed center.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveRadialCritical
import Definitions.Def_Esgk_PlaneCurveSafeComponents
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
def planeCurveExceptionalSample (G : PlanePoly) (a : Point2) (S : Finset Point2) :
    Finset Point2 := by
  classical
  exact S.filter (fun p ↦ p ∈ SingularPointSet G ∨ p ∈ planeRadialCriticalZeroSet G a)


end Esgk


