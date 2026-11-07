-- Prove2me | Definitions.Def_PolygonPack_eucl
-- name    : PolygonPack_eucl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:36.912213+00:00
-- url     : https://prove2.me/theorems/9bc3a84f-3d98-44c2-9848-1e062684f89e
-- title:
--   Euclidean length, the function γ, the deficit, and following a diagonal
-- statement:
--   For points $P,Q$ of the plane, $|PQ|$ is the Euclidean distance. For a length $D$, the paper writes
--   $$
--   \gamma(D)=\sqrt{D^2-1},\qquad \delta=\sqrt2-D .
--   $$
--   A placed segment with coordinate increments $X,Y$ **follows the $u$-diagonal** if $XY>0$, and otherwise the $v$-diagonal.
--
--   **Formalization Note** Mathlib's metric on `ℝ × ℝ` is the sup metric, so Euclidean length is written out as `eucl`. `gam D` has the junk value $0$ when $D<1$, and every statement that uses it has $D\ge1$.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.1, pp.20–21; Lemma A.1, p.21

import Mathlib

namespace PolygonPack

/-- **Euclidean length.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), App. A.1, p.20: "Write D = |AB|". Lemma A.1, p.21: "Put γ(D) = √(D² − 1)".

`eucl P Q` is the Euclidean distance, `gam D` is `γ(D)` and `deficit D` is `δ = √2 − D`.

**Formalization Note.** The metric of `ℝ × ℝ` in Mathlib is the sup metric, so `dist` is never used for a
length here: every length is `eucl`. `gam D` is the junk value `0` when `D < 1`, because `Real.sqrt` of a
negative number is `0`. Every statement that uses it has `1 < D` or `1 ≤ D`. -/
noncomputable def eucl (P Q : ℝ × ℝ) : ℝ := Real.sqrt ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2)

/-- `γ(D) = √(D² − 1)`. -/
noncomputable def gam (D : ℝ) : ℝ := Real.sqrt (D ^ 2 - 1)

/-- The diagonal deficit `δ = √2 − D`. -/
noncomputable def deficit (D : ℝ) : ℝ := Real.sqrt 2 - D

/-- A placed segment follows the `u`-diagonal: its coordinate increments have the same sign (p.21).
Otherwise, by the paper's convention, it follows the `v`-diagonal. -/
def FollowsU (P Q : ℝ × ℝ) : Prop := 0 < (Q.1 - P.1) * (Q.2 - P.2)

end PolygonPack


