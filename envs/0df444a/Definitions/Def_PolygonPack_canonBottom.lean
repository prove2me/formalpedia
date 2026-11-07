-- Prove2me | Definitions.Def_PolygonPack_canonBottom
-- name    : PolygonPack_canonBottom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:28.901463+00:00
-- url     : https://prove2.me/theorems/1c774b4d-aa37-4782-bed0-cc9ff714cb29
-- title:
--   Canonical bottom and canonical pose
-- statement:
--   Let $AB$ be a diameter segment of a polygon of diameter above one. The **canonical bottom** $d$ is the maximum of the bottom coordinate $\min_P v$ over all placements in the unit square with $|\Delta u|\ge|\Delta v|$ for the placed segment, which is $XY\ge0$ for its increments. A **canonical pose** is a placement of that kind which attains $d$.
--
--   These data define the scheduling job of a Tight polygon. Canonical poses need not be unique, so every statement about the vertical span of a canonical pose holds for every maximizer.
--
--   **Formalization Note** The maximum is written as a supremum. It is over a nonempty, bounded set when the polygon fits alone, and it is attained by compactness.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.2, p.22

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_placedUV

namespace PolygonPack

/-- The placed diameter `AB` satisfies `|Δu| ≥ |Δv|`, that is `0 ≤ X·Y` for its increments `X`, `Y`. -/
def ChosenDiag (A B : ℚ × ℚ) (T : Pose) : Prop :=
  0 ≤ ((T.act (castPt B)).1 - (T.act (castPt A)).1) * ((T.act (castPt B)).2 - (T.act (castPt A)).2)

/-- **Canonical bottom.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.2, p.22: "For a Tight polygon, define its canonical pose by maximizing the
bottom coordinate min_P v over all feasible placements with |Δu| ≥ |Δv|. [...] Choose any maximizing pose, and
let d and p denote its bottom coordinate and vertical span, respectively."

`canonBottom v A B` is the supremum `d` of the bottom coordinate over rigid placements in the square whose
diameter `AB` has `|Δu| ≥ |Δv|`.

**Formalization Note.** `|Δu| ≥ |Δv|` is `0 ≤ X·Y` since `Δu² − Δv² = 2XY`, and it allows both signs of `X, Y`,
hence a half-turn (p.47). The supremum is taken over a nonempty and bounded set whenever the polygon fits alone
(a quarter-turn exchanges the diagonals, p.22). It is attained, by compactness. The sanity file proves bounded
above in general. -/
noncomputable def canonBottom (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) : ℝ :=
  sSup {d | ∃ T, IsPlacement v T ∧ ChosenDiag A B T ∧ d = vBottom (placedUV v T)}

/-- `T` is a canonical pose: a placement with `|Δu| ≥ |Δv|` that attains the canonical bottom. "If several poses
maximize d, any of them may be chosen" (p.47), so every statement quantifies over all such `T`. -/
def IsCanonicalPose (v : List (ℚ × ℚ)) (A B : ℚ × ℚ) (T : Pose) : Prop :=
  IsPlacement v T ∧ ChosenDiag A B T ∧ vBottom (placedUV v T) = canonBottom v A B

end PolygonPack


