-- Prove2me | Definitions.Def_SilverRateSC_arcK
-- name    : SilverRateSC_arcK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:44.730548+00:00
-- url     : https://prove2.me/theorems/4a7c967d-a15f-4ed9-ac38-6748baf2fb05
-- title:
--   The arc and the set $K$ of the bending construction
-- statement:
--   Let $0<\beta\le1/4$ and $R=1+\beta$. The **arc** is the shorter arc of the circle with centre $(\beta,\beta)$ and radius $R$ joining $(c_\beta,0)$ to $(\beta,-1)$; explicitly it consists of the points $(p,q)$ of that circle with $p\ge\beta$ and $-1\le q\le0$. The set $K$ is the convex hull of the origin and this arc.
--
--   The gradients of the bending component are scaled points of this arc, and $K$ is the set whose support function generates the component (Lemma A.2).
--
--   **Formalization Note** On the circle, $q=0$ forces $p=c_\beta$ and $q=-1$ forces $p=\beta$; the arc spans less than a quarter turn, so the two conditions $p\ge\beta$, $-1\le q\le0$ cut out exactly the shorter arc.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §A.1, p.29

import Mathlib
import Definitions.Def_SilverRateSC_aBeta

namespace SilverRateSC

/-- **The arc**: the shorter arc of the circle with center `(β, β)` and radius `R = 1 + β`
joining `(c_β, 0)` to `(β, −1)`, i.e. the points `(p, q)` of that circle with `p ≥ β` and
`−1 ≤ q ≤ 0`. -/
def arcPts (β : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | (z 0 - β) ^ 2 + (z 1 - β) ^ 2 = RBeta β ^ 2 ∧ β ≤ z 0 ∧ -1 ≤ z 1 ∧ z 1 ≤ 0}

/-- **The set `K`** of the bending construction: the convex hull of the origin and the shorter
arc of the circle with center `(β, β)` and radius `R = 1 + β` joining `(c_β, 0)` to `(β, −1)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §A.1, p. 29: "Let K be the convex hull of the origin and the shorter arc of this
circle joining (cβ,0) to (β,−1)."

**Formalization Note** `ℝ²` is `EuclideanSpace ℝ (Fin 2)`, coordinate `0` first. On the circle,
the conditions `p ≥ β`, `−1 ≤ q ≤ 0` cut out exactly the arc between the two endpoints: `q = 0`
forces `p = β + √(1 + 2β) = c_β`, `q = −1` forces `p = β`, and the arc spans less than a
quarter turn, so it is the shorter one. -/
def arcK (β : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ ({0} ∪ arcPts β)

end SilverRateSC


