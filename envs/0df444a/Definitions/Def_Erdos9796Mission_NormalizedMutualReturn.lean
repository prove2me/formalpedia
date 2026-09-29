-- Prove2me | Definitions.Def_Erdos9796Mission_NormalizedMutualReturn
-- name    : Erdos9796Mission_NormalizedMutualReturn
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-12T21:33:12.540672+00:00
-- url     : https://prove2.me/theorems/a40287f1-41d7-4747-9f4f-75857c97b51e
-- title:
--   Coordinate points in the Euclidean plane
-- statement:
--   Define the planar point with real coordinates x and y. This notation records the normalized affine chart used by the two-circle obstruction.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/743b102037e9c43dd610a4db761433ce35862a99/lean/Erdos9796Proof/Geometry/SimilarityFrame.lean#L23-L24

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission

/-!
# Coordinate points for the normalized mutual-return configuration

This definition is the coordinate constructor used by the affine chart in
`ExactFiveMutualReturnChord`.
-/

open scoped EuclideanGeometry

namespace Erdos9796Mission

/-- The point with coordinates `(x, y)` in the Euclidean plane. -/
noncomputable def planePoint (x y : ℝ) : Plane :=
  EuclideanSpace.single 0 x + EuclideanSpace.single 1 y

end Erdos9796Mission


