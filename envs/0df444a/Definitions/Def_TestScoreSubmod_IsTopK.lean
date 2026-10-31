-- Prove2me | Definitions.Def_TestScoreSubmod_IsTopK
-- name    : TestScoreSubmod_IsTopK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:11.112954+00:00
-- url     : https://prove2.me/theorems/da8d84b5-8fed-4973-b599-f4e607a09b5b
-- title:
--   Greedy selection of the $k$ items with the largest scores
-- statement:
--   For test scores $a=(a_i)_{i\in N}$ and $k\in\mathbb N$, a set $S$ is a **top-$k$ set** if
--
--   1. $|S|=k$, and
--   2. $a_j\le a_i$ for every $i\in S$ and every $j\notin S$.
--
--   These are exactly the sets that greedy selection in decreasing order of the scores can return, for every tie-breaking rule.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.2, p.12; Corollary 1, p.19; Theorem 1, pp.17–18

import Mathlib

namespace TestScoreSubmod

/-- **Greedy selection in decreasing order of test scores** (Sekar, Vojnovic, Yun,
arXiv:1605.07172v4, §2.2, p.12: "select the k items with the highest test scores"; Corollary 1,
p.19; Theorem 1, pp.17–18).

`IsTopK a k S` says that `S` has exactly `k` items and every item outside `S` has a test score
no larger than every item inside `S`. These are exactly the outputs of greedy selection in
decreasing order of `a`, under any tie-breaking rule.

**Formalization Note** No tie-breaking rule is fixed: every theorem about a top-`k` set holds
for every set with this property. -/
def IsTopK {ι : Type*} (a : ι → ℝ) (k : ℕ) (S : Finset ι) : Prop :=
  S.card = k ∧ ∀ i ∈ S, ∀ j ∉ S, a j ≤ a i

end TestScoreSubmod


