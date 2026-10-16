-- Prove2me | Definitions.Def_Esgk_DistanceNewtonPersistentTangentRoots
-- name    : Esgk_DistanceNewtonPersistentTangentRoots
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:57:53.319887+00:00
-- url     : https://prove2.me/theorems/d7d33264-197a-4e82-b2ae-f301ade07462
-- title:
--   Persistent I-tangent polynomial
-- statement:
--   This extracts the homogeneous component at the I-circular local order of a homogenized plane polynomial and dehomogenizes it to a complex one-variable polynomial.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonITangentHomogeneousForm
import Definitions.Def_Esgk_PlaneCircularLocalChart
import Definitions.Def_Esgk_PlaneCircularLocalOrderDegree
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


def circularITangentPolynomial (G : PlanePoly) : Polynomial ℂ :=
  circularChartDehomogenization
    (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))


end Esgk


