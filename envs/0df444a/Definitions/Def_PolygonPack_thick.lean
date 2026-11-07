-- Prove2me | Definitions.Def_PolygonPack_thick
-- name    : PolygonPack_thick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:30.447634+00:00
-- url     : https://prove2.me/theorems/87351519-2c29-4607-8c41-9f6063e18dd5
-- title:
--   Diameter segment and thickness
-- statement:
--   A **diameter segment** of a polygon with vertex list $v$ is a pair of vertices $A,B$ at maximal Euclidean distance $D=|AB|$. With $e=B-A$, the **thickness** of the polygon perpendicular to $AB$ is
--   $$
--   h=\frac1D\Bigl(\max_{z\in v}\det(e,z-A)-\min_{z\in v}\det(e,z-A)\Bigr).
--   $$
--   Since a linear function on a hull takes its extreme values at listed points, redundant points change neither $D$ nor $h$. The verification file of this mission checks this on an example.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.1, p.20; App. E.2, p.47

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_eucl

namespace PolygonPack

/-- **Diameter segment and thickness.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.1, p.20: "Fix a diameter segment AB of each polygon P,
breaking ties arbitrarily. Write D = |AB|, let h be the total thickness of P perpendicular to AB, and put
δ = √2 − D." App. E.2, p.47: for e = B − A, "ω = max_{z∈P} det(e, z − A) − min_{z∈P} det(e, z − A). Then
D = √(e · e), h = ω/D".

`IsDiameterSeg v A B`: `A`, `B` are vertices at maximal Euclidean distance. `lenD A B` is `D`,
`detAt A B z` is `det(e, z − A)` and `thick v A B` is `h`.

**Formalization Note.** Maximum and minimum are taken over the vertex list, and both are attained on a
finite nonempty set when `v` is nonempty. A linear function on the hull takes its extremes at listed
vertices, so a redundant vertex changes neither `D` nor `h`. On an empty list `thick` is a junk value, and
every use has positive area. -/
noncomputable def lenD (A B : ℚ × ℚ) : ℝ := eucl (castPt A) (castPt B)

/-- `A`, `B` are vertices of `v` at maximal Euclidean distance. -/
def IsDiameterSeg (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) : Prop :=
  A ∈ v ∧ B ∈ v ∧ ∀ z ∈ v, ∀ w ∈ v, lenD z w ≤ lenD A B

/-- `det(e, z − A)` for `e = B − A`. -/
def detAt (A B z : ℚ × ℚ) : ℝ :=
  (((B.1 - A.1) * (z.2 - A.2) - (B.2 - A.2) * (z.1 - A.1) : ℚ) : ℝ)

/-- The thickness `h` of the polygon perpendicular to `AB`. -/
noncomputable def thick (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) : ℝ :=
  (sSup (detAt A B '' {z | z ∈ v}) - sInf (detAt A B '' {z | z ∈ v})) / lenD A B

end PolygonPack


