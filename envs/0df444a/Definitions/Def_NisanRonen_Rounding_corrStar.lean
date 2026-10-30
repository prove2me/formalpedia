-- Prove2me | Definitions.Def_NisanRonen_Rounding_corrStar
-- name    : NisanRonen_Rounding_corrStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:00.571115+00:00
-- url     : https://prove2.me/theorems/d9ed3bd8-47d2-4a0d-96c2-011f6483ac14
-- title:
--   The vector $\mathrm{corr}^*(x, t)$
-- statement:
--   For an allocation $x$ and a matrix $t = (t^i_j)$ of times (a type matrix or a matrix of declarations; $t^i_j$ is agent $i$'s time for task $j$), $\mathrm{corr}^*(x, t)$ is the vector with
--
--   $$
--   \mathrm{corr}^*(x, t)_j = t^i_j \qquad \text{for all } i \text{ and } j \in x^i .
--   $$
--
--   Every task is counted at the time of the agent it is allocated to; $g(x, \mathrm{corr}^*(x,t))$ is the make-span of $x$ on the instance $t$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 22, p. 187 (PDF p. 22): "We define corr∗(x, t) of x and t to be the (unique) vector that satisfies corr∗(x, t)_j = t^i_j for all i and j ∈ x^i"

import Mathlib

namespace NisanRonen.Rounding

/-- **The vector corr\*(x, t)** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 22, p. 187: "We define corr∗(x, t)
of x and t to be the (unique) vector that satisfies corr∗(x, t)_j = t^i_j for all i and
j ∈ x^i"). For a type (or declaration) matrix `d : Fin n → Fin k → ℝ` (`d i j` is agent
`i`'s time for task `j`), `corrStar x d j = d (x j) j`: each task at the time of the agent it
is allocated to. -/
def corrStar {n k : ℕ} (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) : Fin k → ℝ :=
  fun j => d (x j) j

end NisanRonen.Rounding


