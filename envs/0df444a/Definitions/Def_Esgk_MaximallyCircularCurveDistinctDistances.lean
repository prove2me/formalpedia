-- Prove2me | Definitions.Def_Esgk_MaximallyCircularCurveDistinctDistances
-- name    : Esgk_MaximallyCircularCurveDistinctDistances
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:00:58.674996+00:00
-- url     : https://prove2.me/theorems/6cdf5183-a822-43fa-96d0-2b5a6e762ff7
-- title:
--   Configuration points lying on a polynomial factor
-- statement:
--   This defines the subset of a finite configuration consisting of points that lie on the zero set of a chosen polynomial factor.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_NormalizedFactorPointSelection
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


def factorPointSet {n : ℕ} (p : Config n) (G : PlanePoly) :
    Finset PachDeZeeuw.Algebraic.Point2 := by
  classical
  exact (factorPointIndices p G).image p


end Esgk


