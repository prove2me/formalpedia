-- Prove2me | Definitions.Def_Esgk_DistanceNewtonElementaryPolynomial
-- name    : Esgk_DistanceNewtonElementaryPolynomial
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:54:18.812514+00:00
-- url     : https://prove2.me/theorems/19f93b54-41e6-4c10-9223-7159c9962a3f
-- title:
--   Elementary distance polynomial from power sums
-- statement:
--   This forms the plane polynomial obtained by applying the Newton elementary-symmetric recursion to the power-sum polynomials of squared distances in a finite configuration.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonPowerSumPolynomial
import Definitions.Def_Esgk_DistanceSquaredMissingMultiset
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_NewtonElementaryFromPowerSums
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}

 
def distanceNewtonElementaryPolynomial (p : Config n) (m : ℕ) : PlanePoly :=
  newtonElementaryFromPowerSums (fun t ↦ distanceNewtonPowerSumPolynomial p t) m


end Esgk


