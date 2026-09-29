-- Prove2me | Definitions.Def_JohnsonApprox_MaxSatGreedy_ExampleK3
-- name    : JohnsonApprox_MaxSatGreedy_ExampleK3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:21:34.587353+00:00
-- url     : https://prove2.me/theorems/b3b0de24-f558-4d26-958b-38a9c7bd4ae6
-- title:
--   The k = 3 lower-bound input for B1 (proof of Theorem 2)
-- statement:
--   The input used on p. 263 of Johnson (1974) to show that the bound of Theorem 2 is attained for $k = 3$:
--   $$S = \{\{x_1, x_2, x_3\}, \{\bar x_1, x_4, x_5\}, \{\bar x_2, x_6, x_7\}, \{\bar x_3, x_8, x_9\}\}.$$
--   Here $x_i$ denotes the positive literal of variable $i$ and $\bar x_i$ its negation.
--
--   Every literal occurs in exactly one clause, so B1 may pick the literals $\bar x_1, \bar x_2, \bar x_3$ in turn.
--
--   **Formalization Note** Variables keep the paper's indices $1,\dots,9$; `x i` and `xbar i` are the positive and negative literals of variable $i$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 263, proof of Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatGreedy

/-- The positive literal `x_i`. -/
def x (i : ℕ) : Shared.Literal := ⟨i, true⟩

/-- The negative literal `x̄_i`. -/
def xbar (i : ℕ) : Shared.Literal := ⟨i, false⟩

/-- The paper's `k = 3` input (p. 263):
`S = {{x_1, x_2, x_3}, {x̄_1, x_4, x_5}, {x̄_2, x_6, x_7}, {x̄_3, x_8, x_9}}`. -/
def exampleK3 : Finset Shared.Clause :=
  {{x 1, x 2, x 3}, {xbar 1, x 4, x 5}, {xbar 2, x 6, x 7}, {xbar 3, x 8, x 9}}

end JohnsonApprox.MaxSatGreedy


