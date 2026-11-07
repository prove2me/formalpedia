-- Prove2me | Definitions.Def_SteinerNav_Covers
-- name    : SteinerNav_Covers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:13.933164+00:00
-- url     : https://prove2.me/theorems/3d2f1df7-5a7d-40be-b5c1-f925a9d46b37
-- title:
--   $\alpha$-covering of a target by an edge, and of a set by a set of neighbors
-- statement:
--   Points live in $\mathbb R^d$ with the Euclidean distance. Fix $\alpha>1$.
--
--   1. An edge $(s,v)$ **$\alpha$-covers** a target $t$ if
--   $$\|v-t\|<\frac{\|s-t\|}{\alpha}.$$
--   2. A set $B$ of points **$\alpha$-covers** a set $T$ **with respect to a source** $s$ if every $t\in T\setminus\{s\}$ is $\alpha$-covered by an edge $(s,v)$ with $v\in B$.
--
--   Covering is the unit of progress of greedy search: an edge that $\alpha$-covers $t$ moves the search a factor $\alpha$ closer to $t$. Every navigability notion of the mission is phrased through it.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` (abbreviated `Pt d`). The inequality is strict, as on the page. The sets $B$, $T$ are finite sets of points.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §3 "The set cover perspective", p.5

import Mathlib

namespace SteinerNav

/-- Points of `ℝ^d` with the Euclidean distance. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The edge `(s, v)` `α`-covers the target `t`: `‖v − t‖ < ‖s − t‖/α` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §3, p.5).
The inequality is strict. -/
def Covers {d : ℕ} (α : ℝ) (s v t : Pt d) : Prop :=
  dist v t < dist s t / α

/-- The set `B` `α`-covers the set `T` with respect to the source `s`: every `t ∈ T \ {s}` is
`α`-covered by an edge `(s, v)` with `v ∈ B` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §3, p.5). -/
def CoversSet {d : ℕ} (α : ℝ) (s : Pt d) (B T : Finset (Pt d)) : Prop :=
  ∀ t ∈ T, t ≠ s → ∃ v ∈ B, Covers α s v t

end SteinerNav


