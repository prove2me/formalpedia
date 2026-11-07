-- Prove2me | Definitions.Def_PolygonPack_Pose
-- name    : PolygonPack_Pose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:22.614812+00:00
-- url     : https://prove2.me/theorems/ba7b367b-1db9-4bcf-9f50-060e75306c85
-- title:
--   Rotation and translation of a polygon
-- statement:
--   A **pose** is a quadruple $(a,b,x,y)$ of real numbers acting on the plane by
--   $$
--   T(u,v)=(au-bv+x,\ bu+av+y).
--   $$
--   It is **rigid** if $a^2+b^2=1$, so that the linear part is a rotation matrix of determinant one. A polygon has a **placement** $T$ if $T$ is rigid and carries the polygon into the unit square $[0,1]^2$.
--
--   Rigid poses are exactly the rotations by arbitrary angles combined with translations. Reflections and resizing are excluded.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. E, E.1, p.46 (the transformation $T_i$)

import Mathlib
import Definitions.Def_PolygonPack_Instance

namespace PolygonPack

/-- **Pose: a rotation and a translation.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. E, E.1, p.46: "For polygon i, introduce four
variables a_i, b_i, x_i, y_i with a_i² + b_i² = 1. A vertex z = (u, v) is transformed to
T_i(z) = (a_i u − b_i v + x_i, b_i u + a_i v + y_i)." and "The rotation matrix has determinant one, so
reflections are excluded."

`Pose.act` is that map, `Pose.IsRigid` the condition `a² + b² = 1`, `unitSq` the unit square,
`placed v T` the image of the polygon and `IsPlacement v T` a rigid pose that keeps it in the square.

**Formalization Note.** No reflection and no scaling can occur: the linear part is a rotation matrix
exactly when `IsRigid` holds, so every statement that uses a pose asks for `IsRigid`. -/
structure Pose where
  /-- cosine of the rotation angle -/
  a : ℝ
  /-- sine of the rotation angle -/
  b : ℝ
  /-- horizontal translation -/
  x : ℝ
  /-- vertical translation -/
  y : ℝ

/-- The transformation `(u, v) ↦ (a u − b v + x, b u + a v + y)`. -/
def Pose.act (T : Pose) (z : ℝ × ℝ) : ℝ × ℝ :=
  (T.a * z.1 - T.b * z.2 + T.x, T.b * z.1 + T.a * z.2 + T.y)

/-- The linear part of the pose is a rotation. -/
def Pose.IsRigid (T : Pose) : Prop := T.a ^ 2 + T.b ^ 2 = 1

/-- The unit square `[0,1]²`. -/
def unitSq : Set (ℝ × ℝ) := Set.Icc 0 1 ×ˢ Set.Icc 0 1

/-- The polygon spanned by `v`, placed by `T`. -/
def placed (v : List (ℚ × ℚ)) (T : Pose) : Set (ℝ × ℝ) := T.act '' hull v

/-- `T` is a rotation and translation that keeps the polygon inside the unit square. -/
def IsPlacement (v : List (ℚ × ℚ)) (T : Pose) : Prop := T.IsRigid ∧ placed v T ⊆ unitSq

end PolygonPack


