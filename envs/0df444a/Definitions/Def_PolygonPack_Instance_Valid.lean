-- Prove2me | Definitions.Def_PolygonPack_Instance_Valid
-- name    : PolygonPack_Instance_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:23.930202+00:00
-- url     : https://prove2.me/theorems/67cf762e-c9ed-4878-a28b-b0ebe374867a
-- title:
--   Valid instance: positive area, individual fit, nonnegative profit
-- statement:
--   A polygon has **positive area** if its interior is nonempty. An instance is **valid** if every polygon has positive area and fits alone in the unit square under some rigid pose, and every profit is nonnegative. The empty instance is valid.
--
--   These are the standing input conditions of the paper. Fitting alone is the condition "each individually fitting into the unit square" on p.1, and positive area is assumed on p.46.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1, and App. E, p.46

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose

namespace PolygonPack

/-- **Valid instance.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §1, p.1: "each individually fitting into the unit square" and "a
nonnegative rational profit", App. E, p.46: "We assume that polygons have positive area."

`PosArea v`: the polygon has nonempty interior, which for a convex set in the plane is positive area.
`I.Valid`: every polygon has positive area and fits alone in the unit square, and every profit is
nonnegative. An empty instance is valid.

**Formalization Note.** The degenerate extension the paper mentions on p.46 is optional there and is
not part of this definition. -/
def PosArea (v : List (ℚ × ℚ)) : Prop := (interior (hull v)).Nonempty

/-- Every polygon has positive area and fits alone, and every profit is nonnegative. -/
def Instance.Valid (I : Instance) : Prop :=
  ∀ P ∈ I, PosArea P.1 ∧ (∃ T, IsPlacement P.1 T) ∧ 0 ≤ P.2

end PolygonPack


