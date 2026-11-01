-- Prove2me | Definitions.Def_GreedyReusableNet_DecayingAvailability
-- name    : GreedyReusableNet_DecayingAvailability
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:44.450428+00:00
-- url     : https://prove2.me/theorems/951d1b27-fe6c-4753-80e3-d12d05c7ec1f
-- title:
--   Assumption 5.3 (Decaying Availability)
-- statement:
--   **Assumption 5.3.** For every arm $i$, every $x\in\mathbb N$ and counts $n\le n'$,
--   $$F_i(x;n)\ \ge\ F_i(x;n'),\qquad F_i(x;n)=\Pr[b\le x],\ b\sim F_i(\cdot\,;n):$$
--   the blocking time after the $n'$-th use stochastically dominates the blocking time after the $n$-th use.
--
--   **Formalization Note** Since blocking times take values in $\mathbb N$, the inequality is required at $x=0$ too; for laws on $\{1,2,\dots\}$, as printed, that case reads $0\ge0$.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 5.3, p.12

import Mathlib
import Definitions.Def_GreedyReusableNet_ProblemInstance

namespace GreedyReusableNet

/-- **Assumption 5.3 (Decaying Availability)** (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1,
p.12): "`∀i ∈ [N]` and `x ∈ ℤ₊₊`, if `n_{t,i} ≤ n′_{t,i}`, then `F_i(x; n_{t,i}) ≥ F_i(x; n′_{t,i})`.
Or equivalently speaking, `F_i(·; n_{t,i})` is stochastically dominated by `F_i(·; n′_{t,i})`."

Here `F_i(x; n) = ℙ(b ≤ x)` for `b ∼ block i n`.

**Formalization Note** The times `b_{t,i}` take values in `ℕ` (see `ProblemInstance`), so the
condition is required at every `x ∈ ℕ`, including `x = 0`; for laws supported on `ℤ₊₊` the case
`x = 0` reads `0 ≥ 0`. -/
def DecayingAvailability {N : ℕ} (I : ProblemInstance N) : Prop :=
  ∀ (i : Fin N) (x n n' : ℕ), n ≤ n' →
    (I.block i n').toOuterMeasure (Set.Iic x) ≤ (I.block i n).toOuterMeasure (Set.Iic x)

end GreedyReusableNet


