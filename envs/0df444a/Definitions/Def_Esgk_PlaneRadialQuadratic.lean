-- Prove2me | Definitions.Def_Esgk_PlaneRadialQuadratic
-- name    : Esgk_PlaneRadialQuadratic
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:27.2946+00:00
-- url     : https://prove2.me/theorems/8c72f668-ea0d-447f-981b-7b63f92bca49
-- title:
--   The radial quadratic form
-- statement:
--   This defines the real plane polynomial $X^2+Y^2$.

-- Extracted dependency interfaces and their necessary proofs.
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

open PachDeZeeuw.Algebraic

 
def planeRadialQuadratic : PlanePoly :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2


end Esgk


