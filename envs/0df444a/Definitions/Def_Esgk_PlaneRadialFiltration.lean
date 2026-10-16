-- Prove2me | Definitions.Def_Esgk_PlaneRadialFiltration
-- name    : Esgk_PlaneRadialFiltration
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:48.033166+00:00
-- url     : https://prove2.me/theorems/65781b14-6e39-401f-bb51-fc38d7e5b71c
-- title:
--   Radial divisibility of homogeneous components
-- statement:
--   This defines the condition that each degree-$d$ homogeneous component is divisible by $(X^2+Y^2)^{d-m}$, where the exponent is truncated natural subtraction and is zero for $d\le m$.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneRadialQuadratic
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


def IsRadiallyFiltered (m : ℕ) (f : PlanePoly) : Prop :=
  ∀ d, planeRadialQuadratic ^ (d - m) ∣ MvPolynomial.homogeneousComponent d f

namespace IsRadiallyFiltered


end IsRadiallyFiltered


end Esgk


