-- Prove2me | Definitions.Def_SzemerediTrotter_Incidence_squares
-- name    : SzemerediTrotter_Incidence_squares
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:48:34.603738+00:00
-- url     : https://prove2.me/theorems/9d28ae0f-53d9-4e9d-90d5-85d8ebaafcc9
-- title:
--   Axis-parallel squares, their interiors, and the points of $\mathcal P$ they contain
-- statement:
--   Fix the coordinate axes of the plane $\mathbb R^2$. A **square** is a closed axis-parallel square
--
--   $$Q(a,b,s) = \{(x_0,x_1) \in \mathbb R^2 : a \le x_0 \le a+s,\ b \le x_1 \le b+s\},$$
--
--   with lower-left corner $(a,b)$ and side length $s$. Its **interior** is the open square $\{(x_0,x_1) : a < x_0 < a+s,\ b < x_1 < b+s\}$.
--
--   For a finite point set $\mathcal P$, the number of points of $\mathcal P$ **contained in** the square $Q$ is $\#(\mathcal P \cap Q)$, and for a finite family $\mathcal Q$ of squares, the points of $\mathcal P$ **covered by** $\mathcal Q$ are those lying in at least one square of $\mathcal Q$; their number is $\#\{p \in \mathcal P : \exists Q \in \mathcal Q,\ p \in Q\}$.
--
--   These are the objects of the covering lemma of Szemerédi and Trotter (Section 2), where "square" means a square with sides parallel to the chosen coordinate axes.
--
--   **Formalization Note** A square is encoded by the triple $(a,b,s) \in \mathbb R \times \mathbb R \times \mathbb R$; the side $s$ is not restricted here, and the covering lemma requires $s > 0$ of each square it produces. "Contains" and "covered" refer to the closed square, "interior" to the open one. The counts use classical decidability.
-- source:
--   Szemerédi, Trotter, Extremal Problems in Discrete Geometry, Combinatorica 3 (1983), p. 382, Section 2 (squares with sides parallel to the coordinate axes; Lemma)

import Mathlib
import Definitions.Def_SzemerediTrotter_Incidence_incidences

namespace SzemerediTrotter.Incidence

open Classical

/-- The closed axis-parallel square with lower-left corner `(a, b)` and side `s`, where
`q = (a, b, s)`: the points `x` with `a ≤ x 0 ≤ a + s` and `b ≤ x 1 ≤ b + s`. -/
def closedSquare (q : ℝ × ℝ × ℝ) : Set Plane :=
  {x | q.1 ≤ x 0 ∧ x 0 ≤ q.1 + q.2.2 ∧ q.2.1 ≤ x 1 ∧ x 1 ≤ q.2.1 + q.2.2}

/-- The interior of the square `q = (a, b, s)`: the points `x` with `a < x 0 < a + s` and
`b < x 1 < b + s`. -/
def openSquare (q : ℝ × ℝ × ℝ) : Set Plane :=
  {x | q.1 < x 0 ∧ x 0 < q.1 + q.2.2 ∧ q.2.1 < x 1 ∧ x 1 < q.2.1 + q.2.2}

/-- The number of points of `𝒫` contained in the closed square `q`. -/
noncomputable def pointsInSquare (P : Finset Plane) (q : ℝ × ℝ × ℝ) : ℕ :=
  (P.filter (fun p => p ∈ closedSquare q)).card

/-- The number of points of `𝒫` covered by (the closed squares of) the family `𝒬`. -/
noncomputable def coveredPoints (P : Finset Plane) (Q : Finset (ℝ × ℝ × ℝ)) : ℕ :=
  (P.filter (fun p => ∃ q ∈ Q, p ∈ closedSquare q)).card

end SzemerediTrotter.Incidence


