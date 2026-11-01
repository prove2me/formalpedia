-- Prove2me | Definitions.Def_SubmodOrder_algorithm1
-- name    : SubmodOrder_algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:44.587442+00:00
-- url     : https://prove2.me/theorems/66ed6726-137f-4c2a-adc0-be68894e48f1
-- title:
--   Algorithm 1: $\tfrac12$ for Cardinality
-- statement:
--   Let $k\ge1$ be a cardinality and $\varepsilon\in(0,1)$. **Algorithm 1** sets
--
--   $$
--   \tau=\frac1k\max_{e\in N}f(\{e\}),\qquad L=\max\bigl(1,\lceil\log_{1+\varepsilon}k\rceil\bigr),
--   $$
--
--   runs Threshold Add$(k,(1+\varepsilon)^{i-1}\tau)$ for $i=1,\dots,L$, obtaining sets $S_1,\dots,S_L$, and outputs the best of them, i.e. one of largest value.
--
--   Theorem 2 shows that this is a $(1-\varepsilon)\frac12$-approximation for monotone subadditive maximization under a cardinality constraint when $\pi$ is a weak submodular order, with $O(\frac n\varepsilon\log k)$ queries.
--
--   **Formalization Note** The algorithm is a value-oracle program built from $\pi$, $k$ and $\varepsilon$ only. It first queries the $n$ singletons and takes $\tau=\max(0,\max_e f(\{e\}))/k$. The printed loop runs to $\lceil\log_{1+\varepsilon}k\rceil$, which is $0$ at $k=1$, where the loop would be empty; the `max` with $1$ corrects this and changes nothing for $k\ge2$. "Best of" compares the values returned by Threshold Add, and ties go to the first maximizer.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Algorithm 1, p.13

import Mathlib
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd

namespace SubmodOrder

/-- The number of thresholds of Algorithm 1, `L = max(1, ⌈log_{1+ε} k⌉)` (Udwani,
arXiv:2107.02743v5, Algorithm 1, p.13, loop `i ∈ {1, 2, · · · , ⌈log1+ε k⌉}`).

**Formalization Note.** The `max` with `1` corrects the case `k = 1`, where `⌈log_{1+ε} 1⌉ = 0`,
the printed loop is empty and its "Best of" is undefined; for `k ≥ 2` it is the printed bound. -/
noncomputable def numRounds (k : ℕ) (ε : ℝ) : ℕ :=
  max 1 ⌈Real.logb (1 + ε) k⌉₊

/-- Queries the singletons `{e}` in the order of the list and returns
`max(m, max_e f({e}))`. -/
def singletonMaxProg {α : Type*} : List α → ℝ → OracleProg α ℝ
  | [], m => OracleProg.pure m
  | e :: es, m => OracleProg.query {e} fun v => singletonMaxProg es (max m v)

/-- Runs Threshold Add for each threshold of the list in turn, keeping the best pair
`(S, f(S))` seen so far; a later set replaces the current best only if its value is strictly
larger (so ties go to the first maximizer). -/
noncomputable def bestLoop {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ) :
    List ℝ → Finset α × ℝ → OracleProg α (Finset α × ℝ)
  | [], best => OracleProg.pure best
  | t :: ts, best =>
    OracleProg.bind (thresholdAdd π k t) fun r =>
      bestLoop π k ts (if best.2 < r.2 then r else best)

/-- Algorithm 1, "1/2 for Cardinality" (Udwani, arXiv:2107.02743v5, p.13):

```
Input: Cardinality k, error ε ∈ (0,1);
Initialize τ = 1/k max_{e∈N} f({e});
for i ∈ {1, 2, · · · , ⌈log1+ε k⌉} do
  Si = Threshold Add(k, (1 + ε)^{i−1} τ);
end
Output: Best of {S1, S2, · · · , S⌈log1+ε k⌉}
```

**Formalization Note.** The program first queries the `n` singletons and sets
`τ = max(0, max_e f({e}))/k`. It then runs Threshold Add with the thresholds
`(1 + ε)^{i−1} τ` for `i = 1, …, L`, `L = numRounds k ε = max(1, ⌈log_{1+ε} k⌉)` (the `max` with
`1` corrects `k = 1`), and returns the first set of largest value among `S_1, …, S_L`, compared
by the values cached by Threshold Add. The program is built from `π`, `k` and `ε` only, never
from `f`. -/
noncomputable def algorithm1 {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (ε : ℝ) : OracleProg α (Finset α) :=
  OracleProg.bind (singletonMaxProg (orderList π) 0) fun M =>
    OracleProg.bind (thresholdAdd π k (M / k)) fun r₁ =>
      OracleProg.bind
        (bestLoop π k ((List.range (numRounds k ε - 1)).map fun j => (1 + ε) ^ (j + 1) * (M / k))
          r₁)
        fun r => OracleProg.pure r.1

end SubmodOrder


