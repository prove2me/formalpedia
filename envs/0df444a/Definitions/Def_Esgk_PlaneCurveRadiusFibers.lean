-- Prove2me | Definitions.Def_Esgk_PlaneCurveRadiusFibers
-- name    : Esgk_PlaneCurveRadiusFibers
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:00:25.968868+00:00
-- url     : https://prove2.me/theorems/111c6c85-165d-4afc-a8de-666c331c9947
-- title:
--   Fibers of squared radius on a plane curve
-- statement:
--   This defines the points of a polynomial curve whose squared distance from a specified center equals a specified real value.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
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

 
def planeCurveSquaredRadiusFiber (G : PlanePoly) (a : Point2) (r : ℝ) : Set Point2 :=
  {p | p ∈ PlaneCurveZeroSet G ∧ dist p a ^ 2 = r}


end Esgk


