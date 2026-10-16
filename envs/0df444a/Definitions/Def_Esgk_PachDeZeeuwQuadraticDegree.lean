-- Prove2me | Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
-- name    : Esgk_PachDeZeeuwQuadraticDegree
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:38.851292+00:00
-- url     : https://prove2.me/theorems/3460f25d-3a83-4074-a9ea-0630d929a8f3
-- title:
--   Incidence data supported on one curve
-- statement:
--   For prepared bipartite incidence data, this defines the condition that the two supporting curves are the same set.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace Esgk

open EuclideanGeometry PachDeZeeuw

 
def SelfCurvePreparedInput {d : ℕ} (X : PreparedBipartiteInput d) : Prop :=
  X.C₁ = X.C₂


end Esgk


