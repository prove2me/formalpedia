-- Prove2me | Definitions.Def_Esgk_CircularJTangentConjugation
-- name    : Esgk_CircularJTangentConjugation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:57:45.659988+00:00
-- url     : https://prove2.me/theorems/d85177cc-0396-4748-9082-1e541f809db9
-- title:
--   Polynomial at the complex circular tangent direction
-- statement:
--   This defines the one-variable complex polynomial obtained by evaluating a complexified plane polynomial on the circular J-tangent chart.

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

namespace MvPolynomial


end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic Polynomial

variable {n : ℕ}


def circularJTangentPolynomial (G : PlanePoly) : Polynomial ℂ :=
  circularChartDehomogenization
    (MvPolynomial.homogeneousComponent (planeCircularLocalOrderJ G)
      (projectiveCircularChartJ (planeHomogenization G.totalDegree G)))


end Esgk


