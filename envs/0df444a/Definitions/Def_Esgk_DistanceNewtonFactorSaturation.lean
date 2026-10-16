-- Prove2me | Definitions.Def_Esgk_DistanceNewtonFactorSaturation
-- name    : Esgk_DistanceNewtonFactorSaturation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:58:39.333983+00:00
-- url     : https://prove2.me/theorems/34663a4d-9e85-4144-9053-0776d23f54e9
-- title:
--   Maximal circularity predicate for a plane polynomial
-- statement:
--   This predicate requires the two local orders at the complex circular points to equal half of the polynomial's total degree.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCircularLocalOrderDegree
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


def IsMaximallyCircular (G : PlanePoly) : Prop :=
  2 * planeCircularLocalOrderI G = G.totalDegree ∧
    2 * planeCircularLocalOrderJ G = G.totalDegree


variable {n : ℕ}


end Esgk


