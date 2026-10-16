-- Prove2me | Definitions.Def_LeanFormalizations_Geometry_Euclidean_IsometryClassification
-- name    : LeanFormalizations_Geometry_Euclidean_IsometryClassification
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:13.641885+00:00
-- url     : https://prove2.me/theorems/e0ff76bc-fa0a-4a63-ba62-58739990da89
-- title:
--   The standard orientation of the Euclidean plane
-- statement:
--   This equips the real Euclidean plane with the orientation induced by its standard coordinate basis.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open EuclideanGeometry
open scoped Real InnerProductSpace EuclideanSpace

namespace EuclideanGeometry

 
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)


noncomputable instance : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩

 
local notation "o" => (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

 
local notation "J" => Orientation.rightAngleRotation o


end EuclideanGeometry


