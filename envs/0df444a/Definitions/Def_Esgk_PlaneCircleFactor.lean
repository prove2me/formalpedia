-- Prove2me | Definitions.Def_Esgk_PlaneCircleFactor
-- name    : Esgk_PlaneCircleFactor
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:01:22.769572+00:00
-- url     : https://prove2.me/theorems/d1a1c6f1-cf31-47e0-9039-7ec889be7ea2
-- title:
--   Polynomials defining circles
-- statement:
--   A real plane polynomial is a circle factor when it is associated to a circle equation with nonnegative radius. The definition includes the zero-radius case.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryCircleNoncontainment
import Definitions.Def_Esgk_NormalizedFactorPointSelection
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
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


def IsCircleFactor (G : PlanePoly) : Prop :=
  ∃ c r, 0 ≤ r ∧ Associated G (circleEquationPolynomial c r)


end Esgk


