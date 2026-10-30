-- Prove2me | Definitions.Def_FreedmanTail_partialSum
-- name    : FreedmanTail_partialSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:10.16898+00:00
-- url     : https://prove2.me/theorems/90d500f5-97c7-4479-9a43-3bd8beef9552
-- title:
--   Partial sums $S_n = X_1 + \cdots + X_n$
-- statement:
--   For a sequence of real random variables $X_1, X_2, \dots$ define
--   $$S_n = X_1 + \cdots + X_n , \qquad S_0 = 0 .$$
--
--   **Formalization Note** The sequence is indexed from $0$ in Lean: the Lean variable $X_k$ is the paper's $X_{k+1}$, so the sum of the first $n$ Lean terms is the paper's $S_n$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (1.2) Definition (f), p. 101

import Mathlib

namespace FreedmanTail

/-- **The partial sums `S_n = X_1 + ⋯ + X_n`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(1.2) Definition (f), p. 101: "(f) S_n = X_1 + ··· + X_n, so S_0 = 0".

`partialSum X n ω = ∑_{i < n} X i ω`.

**Formalization Note.** The paper's increments are `X_1, X_2, …`; Lean's `X k` is the paper's
`X_{k+1}`, so `partialSum X n` is the paper's `S_n` for every `n ≥ 0` (empty sum `S_0 = 0`). -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

end FreedmanTail


