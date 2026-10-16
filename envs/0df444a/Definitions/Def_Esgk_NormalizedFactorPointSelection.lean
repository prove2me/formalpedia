-- Prove2me | Definitions.Def_Esgk_NormalizedFactorPointSelection
-- name    : Esgk_NormalizedFactorPointSelection
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:00:07.643737+00:00
-- url     : https://prove2.me/theorems/b4de88cb-093c-4d96-88b5-3d25322dd687
-- title:
--   Sample indices lying on a polynomial zero set
-- statement:
--   For an indexed finite planar sample and a real plane polynomial, this defines the finite set of indices whose sample points lie on the polynomial’s zero set.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
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


def factorPointIndices (p : Fin n → Point2) (G : PlanePoly) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun i ↦ p i ∈ PlaneCurveZeroSet G


end Esgk


