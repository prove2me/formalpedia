-- Prove2me | Definitions.Def_Esgk_PlaneCurveRadialCritical
-- name    : Esgk_PlaneCurveRadialCritical
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:16.753968+00:00
-- url     : https://prove2.me/theorems/6a8cb766-d459-4ebc-a60c-b26ca91c7402
-- title:
--   The radial-critical polynomial of a plane curve
-- statement:
--   For a plane polynomial $G$ and a center $a$, this defines $(X-a_1)G_Y-(Y-a_2)G_X$ and its common zero set with $G$. On the regular curve, this polynomial detects critical points of squared distance from $a$.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

 
def planeRadialCritical (G : PlanePoly) (a : Point2) : PlanePoly :=
  (X 0 - C (a 0)) * pderiv (1 : Fin 2) G -
    (X 1 - C (a 1)) * pderiv (0 : Fin 2) G

 
def planeRadialCriticalZeroSet (G : PlanePoly) (a : Point2) : Set Point2 :=
  PlaneCurveZeroSet G ∩ PlaneCurveZeroSet (planeRadialCritical G a)


end Esgk


