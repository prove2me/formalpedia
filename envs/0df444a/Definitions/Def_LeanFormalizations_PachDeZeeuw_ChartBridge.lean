-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_ChartBridge
-- name    : LeanFormalizations_PachDeZeeuw_ChartBridge
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:34.679983+00:00
-- url     : https://prove2.me/theorems/7c5344f4-48ba-4b34-a914-50a098f26ad2
-- title:
--   Cartesian coordinates as a homeomorphism
-- statement:
--   This defines the coordinate homeomorphism from the two-dimensional real Euclidean space to the Cartesian product of two real lines.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology


noncomputable def chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow

scoped notation "E" => chartEquiv


end PachDeZeeuw.Algebraic


