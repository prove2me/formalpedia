-- Prove2me | Definitions.Def_GreedyReusableNet_prob
-- name    : GreedyReusableNet_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:58.046719+00:00
-- url     : https://prove2.me/theorems/e260368d-79ac-48fa-84a4-7d3627c9d74e
-- title:
--   Marginal activation probability $\mathbb P_t(B\mid\mathcal A,n(B))$
-- statement:
--   For the data $d$ of a period, a bundle $B$, an action set $\mathcal A$ and a counting vector $n$, the **marginal activation probability** is
--   $$\mathbb P_t(B\mid\mathcal A,n(B))=\Pr\big[B\in\mathcal A_{\mathrm{act}}\big],\qquad \mathcal A_{\mathrm{act}}\sim\text{activation law of }(\mathcal A,n),$$
--   the probability that $B$ is among the activated bundles, eq. (1) of the paper. It enters the per-period objective $\sum_{B\in\mathcal A}f(B)\,\mathbb P_t(B\mid\mathcal A,n(B))$ of the oracle and Assumptions 2 and 5.2.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, eq. (1), p.9

import Mathlib
import Definitions.Def_GreedyReusableNet_PeriodData

namespace GreedyReusableNet

/-- **The marginal activation probability** `ℙ_t(B | 𝒜, n(B)) = 𝔼_t[𝟙_t{B} | 𝒜, n]` of (1)
(Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, eq. (1), p.9): the probability that bundle `B` is
among the activated bundles when the action set `A` is taken at counting vector `n`.

**Formalization Note** It is the marginal of the period's activation law `d.act A n`, so the
oracle's objective and Assumptions 2 and 5.2 refer to the same mechanism the process samples
from. -/
noncomputable def prob {N : ℕ} (d : PeriodData N) (B : Finset (Fin N))
    (A : Finset (Finset (Fin N))) (n : Fin N → ℕ) : ℝ :=
  ((d.act A n).toOuterMeasure {S | B ∈ S}).toReal

end GreedyReusableNet


