-- Prove2me | Definitions.Def_Esgk_CollisionRootGroupoid
-- name    : Esgk_CollisionRootGroupoid
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:51:45.478914+00:00
-- url     : https://prove2.me/theorems/d9b05806-631e-4a8b-bf59-b807a82fb221
-- title:
--   Linear parts under composition of plane isometries
-- statement:
--   The linear part of a composite plane isometry is identified with the composite of the two linear parts.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DirectIsometryClassification
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

noncomputable section

variable {n : ℕ} {A : ℝ}


theorem planeIsometryLinearPart_trans (g h : IsometryEquiv ℝ² ℝ²) :
    planeIsometryLinearPart (g.trans h) =
      (planeIsometryLinearPart g).trans (planeIsometryLinearPart h) := by
  have key : ∀ (k : IsometryEquiv ℝ² ℝ²) (y : ℝ²),
      planeIsometryLinearPart k y = k y - k 0 :=
    fun k y ↦ eq_sub_iff_add_eq.mpr (planeIsometry_apply_eq_linearPart_add k y).symm
  ext x
  rw [key (g.trans h) x, LinearIsometryEquiv.trans_apply, key g x, map_sub,
    key h (g x), key h (g 0), IsometryEquiv.trans_apply, IsometryEquiv.trans_apply]
  abel_nf


end

end Esgk


