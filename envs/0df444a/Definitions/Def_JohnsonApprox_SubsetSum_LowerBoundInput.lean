-- Prove2me | Definitions.Def_JohnsonApprox_SubsetSum_LowerBoundInput
-- name    : JohnsonApprox_SubsetSum_LowerBoundInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:17:19.372291+00:00
-- url     : https://prove2.me/theorems/22ce8d28-1d05-431c-92ea-7d6687194828
-- title:
--   The lower-bound input for A_k: sizes 1 + ε, 1, …, 1 and b = k + 1 (proof of Theorem 1)
-- statement:
--   This is the family of SUBSET-SUM inputs used by Johnson (1974) in the proof of Theorem 1 to show that the bound $(k+1)/k$ for algorithm $A_k$ cannot be improved:
--
--   > For the lower bound on the limit, consider the input ⟨T, s, b⟩ where T = {a_1, ..., a_{k+2}}, s(a_i) = 1 + ε for i = 1, 1 otherwise, b = k + 1.
--
--   For a natural number $k$ and a rational $\varepsilon > 0$, the input has $k+2$ elements $a_1, \dots, a_{k+2}$, sizes
--
--   $$s(a_1) = 1 + \varepsilon, \qquad s(a_i) = 1 \quad (2 \le i \le k+2),$$
--
--   and bound $b = k + 1$.
--
--   With these sizes the only element larger than $b/(k+1) = 1$ is $a_1$ (the elements of size exactly $1$ are not big), which is what drives the behaviour of $A_k$ on this input.
--
--   **Formalization Note** The ground set is `Fin (k + 2)` with all its elements, and $a_1$ is the index `0`. The hypothesis $\varepsilon > 0$ is part of the construction because it makes every size positive, as an input requires; the theorem about this input additionally assumes $\varepsilon < 1$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 261, proof of Theorem 1 (lower-bound input)

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem

namespace JohnsonApprox.SubsetSum

/-- The lower-bound input of the proof of Theorem 1 (Johnson 1974, p. 261):
`T = {a_1, …, a_{k+2}}` (here `Fin (k + 2)`, with `a_1` the index `0`),
`s(a_1) = 1 + ε`, `s(a_i) = 1` otherwise, and `b = k + 1`. -/
def lowerBoundInput (k : ℕ) (ε : ℚ) (hε : 0 < ε) : Input (Fin (k + 2)) where
  T := Finset.univ
  s := fun i => if i = 0 then 1 + ε else 1
  b := (k : ℚ) + 1
  s_pos := by
    intro x _
    split_ifs <;> linarith
  b_pos := by positivity

end JohnsonApprox.SubsetSum


