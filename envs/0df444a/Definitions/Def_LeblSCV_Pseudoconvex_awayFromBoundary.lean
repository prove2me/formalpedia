-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_awayFromBoundary
-- name    : LeblSCV_Pseudoconvex_awayFromBoundary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:42:27.622869+00:00
-- url     : https://prove2.me/theorems/d8fc9c17-5eae-46c9-989b-03308c2a3d54
-- title:
--   The set $U_\epsilon$ of points further than $\epsilon$ from $\partial U$
-- statement:
--   For an open $U \subset \mathbb{C}^n$ and $\epsilon \in \mathbb{R}$, $U_\epsilon \subset U$ is the set of points of $U$ further than $\epsilon$ away from $\partial U$ in the Euclidean distance:
--   $$U_\epsilon = \{ z \in U : \|z - w\| > \epsilon \text{ for all } w \in \partial U \}.$$
--
--   It is the domain of the smoothed functions $f_\epsilon$ in Theorem 2.4.10.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. The condition is written with “for all $w \in \partial U$” rather than `Metric.infDist z (frontier U) > ε`. This gives $U_\epsilon = U$ when $\partial U = \emptyset$ (e.g. $U = \mathbb{C}^n$), instead of the junk value $\operatorname{infDist}(z, \emptyset) = 0$. When $\partial U \neq \emptyset$ the two agree, because $\partial U$ is closed and the distance is attained.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 85, Theorem 2.4.10

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- The set `U_ε ⊂ U` of points further than `ε` away from `∂U` (Lebl, p. 85, Theorem 2.4.10),
for the Euclidean distance of `ℂⁿ = EuclideanSpace ℂ (Fin n)`: `z ∈ U` with `dist(z, w) > ε` for
every `w ∈ ∂U`. Written with `∀ w ∈ ∂U` rather than `Metric.infDist`, so that `U_ε = U` when
`∂U = ∅` (instead of the junk value `infDist z ∅ = 0`); for nonempty `∂U` the two agree, since
`∂U` is closed and the infimum is attained. -/
def awayFromBoundary {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (ε : ℝ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | z ∈ U ∧ ∀ w ∈ frontier U, ε < dist z w}

end LeblSCV.Pseudoconvex


