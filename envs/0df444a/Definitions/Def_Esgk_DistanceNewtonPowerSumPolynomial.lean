-- Prove2me | Definitions.Def_Esgk_DistanceNewtonPowerSumPolynomial
-- name    : Esgk_DistanceNewtonPowerSumPolynomial
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:30.180978+00:00
-- url     : https://prove2.me/theorems/eb4f915f-9d50-4a24-b5be-3230af3aad1d
-- title:
--   Power-sum polynomial for squared distances
-- statement:
--   For a finite configuration and a nonnegative exponent, this defines the plane polynomial formed from the corresponding power sum of squared distances and the ordered distinct-distance values.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceDeficiencyNewton
import Definitions.Def_Esgk_Energy
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
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
open scoped BigOperators

variable {n : ℕ}


def distanceNewtonPowerSumPolynomial (p : Config n) (t : ℕ) : PlanePoly :=
  MvPolynomial.C (3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ t) -
    ∑ q : Fin n, (planeSquaredDistancePolynomial (p q)) ^ t


end Esgk


