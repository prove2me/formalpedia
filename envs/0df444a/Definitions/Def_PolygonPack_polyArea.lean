-- Prove2me | Definitions.Def_PolygonPack_polyArea
-- name    : PolygonPack_polyArea
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:33.161174+00:00
-- url     : https://prove2.me/theorems/dade3495-79f1-40ed-8cf7-0fc40cb39bfc
-- title:
--   Area of a polygon
-- statement:
--   The **area** of a polygon is the two-dimensional Lebesgue measure of its convex hull, as a real number.
--
--   **Formalization Note** The vertex list is unordered, so a shoelace formula is not used.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §1.1, p.2

import Mathlib
import Definitions.Def_PolygonPack_Instance

namespace PolygonPack

/-- **Area of a polygon.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §1.1, p.2: "area(P) its area".

**Formalization Note.** Lebesgue measure of the hull in `ℝ × ℝ`. A shoelace formula would be wrong here,
because the vertex list is unordered. The hull is compact, so the measure is finite and `toReal` is the
real area. -/
noncomputable def polyArea (v : List (ℚ × ℚ)) : ℝ := (MeasureTheory.volume (hull v)).toReal

end PolygonPack


