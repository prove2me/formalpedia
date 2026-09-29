-- Prove2me | Definitions.Def_JohnsonApprox_MaxSatWeighted_ExampleK3
-- name    : JohnsonApprox_MaxSatWeighted_ExampleK3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:13:50.133985+00:00
-- url     : https://prove2.me/theorems/502d02f3-6d93-4c09-84be-63d60bdc1e12
-- title:
--   The k = 3 lower-bound input for algorithm B2 (proof of Theorem 3)
-- statement:
--   The lower-bound input used in the proof of Theorem 3 (p. 264) is the set of eight clauses
--   $$S = \{\{x_1, x_2, x_3\}, \{\bar x_1, x_4, x_5\}, \{x_1, \bar x_2, x_3\}, \{\bar x_1, x_6, x_7\}, \{x_1, x_2, \bar x_3\}, \{\bar x_1, x_8, x_9\}, \{x_1, \bar x_2, \bar x_3\}, \{\bar x_1, x_{10}, x_{11}\}\},$$
--   "where $x_1$ occurs in clauses with all possible combinations of a literal from $\{x_2, \bar x_2\}$ and one from $\{x_3, \bar x_3\}$, and $\bar x_1$ occurs in an equal number of clauses, each filled out with new literals."
--
--   It is the instance on which B2 attains the ratio $8/7 = 2^3/(2^3-1)$.
--
--   **Formalization Note** `lit i` is $x_i$ and `nlit i` is $\bar x_i$; the variable index is the paper's subscript.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 264, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatWeighted

/-- The positive literal `x_i`. -/
def lit (i : ℕ) : Shared.Literal := ⟨i, true⟩

/-- The negative literal `x̄_i`. -/
def nlit (i : ℕ) : Shared.Literal := ⟨i, false⟩

/-- The lower-bound input for `k = 3` from the proof of Theorem 3 (p. 264):
`S = {{x_1, x_2, x_3}, {x̄_1, x_4, x_5}, {x_1, x̄_2, x_3}, {x̄_1, x_6, x_7},
{x_1, x_2, x̄_3}, {x̄_1, x_8, x_9}, {x_1, x̄_2, x̄_3}, {x̄_1, x_10, x_11}}`.
Variable `x_i` is the variable with index `i`. -/
def exampleK3 : Finset Shared.Clause :=
  {{lit 1, lit 2, lit 3}, {nlit 1, lit 4, lit 5},
   {lit 1, nlit 2, lit 3}, {nlit 1, lit 6, lit 7},
   {lit 1, lit 2, nlit 3}, {nlit 1, lit 8, lit 9},
   {lit 1, nlit 2, nlit 3}, {nlit 1, lit 10, lit 11}}

end JohnsonApprox.MaxSatWeighted


