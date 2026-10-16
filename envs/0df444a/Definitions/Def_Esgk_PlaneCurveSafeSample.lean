-- Prove2me | Definitions.Def_Esgk_PlaneCurveSafeSample
-- name    : Esgk_PlaneCurveSafeSample
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:09.656694+00:00
-- url     : https://prove2.me/theorems/fb924b05-41c0-48f7-b386-d3f6c29fd03a
-- title:
--   A sample lifted to the regular curve locus
-- statement:
--   This removes singular and radial-critical points from a finite sample and lifts the remaining points that lie on the curve to its regular-locus subtype.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveExceptionalSample
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

open Set MvPolynomial
open scoped Classical
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
def planeCurveSafeSample (G : PlanePoly) (o : Point2) (S : Finset Point2) :
    Finset (planeCurveRegularLocus G) :=
  (S \ planeCurveExceptionalSample G o S).preimage Subtype.val Subtype.val_injective.injOn


end Esgk


