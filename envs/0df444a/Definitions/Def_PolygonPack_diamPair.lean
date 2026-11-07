-- Prove2me | Definitions.Def_PolygonPack_diamPair
-- name    : PolygonPack_diamPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:27.628241+00:00
-- url     : https://prove2.me/theorems/2252ada2-908a-48d2-a951-1e5b4f18b9ad
-- title:
--   The fixed diameter of a polygon
-- statement:
--   The **fixed diameter** of a polygon is the first pair of its vertex list, in input order, that has maximal squared distance. The numbers $D(P)$, $h(P)$ and $\delta(P)=\sqrt2-D(P)$ are read from that pair, and they enter the classification of polygons.
--
--   **Formalization Note** On p.20 ties are broken arbitrarily, and on p.47 they are broken by input order. Reordering a vertex list realizes any tie break, so the rule loses nothing.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. E.2, p.47

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick

namespace PolygonPack

/-- Squared distance of two rational points. -/
def distSqQ (z w : ℚ × ℚ) : ℚ := (w.1 - z.1) ^ 2 + (w.2 - z.2) ^ 2

/-- **The polygon's fixed diameter.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. E.2, p.47: "For preprocessing, find a diameter by comparing
squared distances of vertex pairs, breaking ties by input order."

`diamPair v` is the first pair of `v ×ˢ v` of maximal squared distance. `polyD`, `polyH`, `polyDelta` are
`D(P)`, `h(P)`, `δ(P)` for that diameter.

**Formalization Note.** On p.20 ties are broken "arbitrarily". Reordering the vertex list realizes any
tie break, so the input-order rule loses nothing. On an empty list the value is the default `((0,0),(0,0))`,
and no valid instance has an empty list. -/
def diamPair (v : List (ℚ × ℚ)) : (ℚ × ℚ) × (ℚ × ℚ) :=
  ((v ×ˢ v).find? (fun p => decide (∀ q ∈ v ×ˢ v, distSqQ q.1 q.2 ≤ distSqQ p.1 p.2))).getD ((0, 0), (0, 0))

/-- The diameter `D(P)`. -/
noncomputable def polyD (v : List (ℚ × ℚ)) : ℝ := lenD (diamPair v).1 (diamPair v).2

/-- The thickness `h(P)`. -/
noncomputable def polyH (v : List (ℚ × ℚ)) : ℝ := thick v (diamPair v).1 (diamPair v).2

/-- The diagonal deficit `δ(P)`. -/
noncomputable def polyDelta (v : List (ℚ × ℚ)) : ℝ := deficit (polyD v)

end PolygonPack


