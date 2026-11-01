-- Prove2me | Definitions.Def_GreedyReusableNet_Oracle
-- name    : GreedyReusableNet_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:04.423456+00:00
-- url     : https://prove2.me/theorems/1506d667-6924-4ce4-b9d8-eff2c8a1dcb2
-- title:
--   Randomized per-period optimization oracle
-- statement:
--   An **oracle** receives one period's data, a weight function $f$ on bundles, a counting vector $n$, the set of available arms and a seed $u$, and returns an action set. It is meant to approximately solve
--   $$\max_{\mathcal A\in\mathscr A_t,\ \mathcal A\text{ available}}\ \sum_{B\in\mathcal A}f(B)\,\mathbb P_t(B\mid\mathcal A,n(B)).$$
--   Its guarantee is `IsApproxOracle`.
--
--   **Formalization Note** The output is a measurable function of the seed, as the output of any randomized algorithm is a function of its random bits.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Assumption 4, p.11

import Mathlib
import Definitions.Def_GreedyReusableNet_PeriodData

namespace GreedyReusableNet

/-- **A randomized optimization oracle** for the per-period problem (Simchi-Levi, Zheng & Zhu,
SSRN 3981123, Assumption 4, p.11). Given one period's data `d`, a weight function `f` on bundles,
a counting vector `n` and the set `free` of available arms, and a seed `u` (uniform on `[0, 1]`),
it returns an action set. Its approximation guarantee is `IsApproxOracle`.

**Formalization Note** The oracle reads one period's data only. It is a measurable function of its
seed (an algorithm's output is determined by its random bits); this is what makes the expected
reward of a policy that calls it well defined. -/
structure Oracle (N : ℕ) where
  /-- the returned action set for period data, weights, counts, free arms and seed -/
  sel : PeriodData N → (Finset (Fin N) → ℝ) → (Fin N → ℕ) → Finset (Fin N) → ℝ →
    Finset (Finset (Fin N))
  /-- the output is a measurable function of the seed -/
  measurable_sel : ∀ (d : PeriodData N) (f : Finset (Fin N) → ℝ) (n : Fin N → ℕ)
    (free : Finset (Fin N)) (A : Finset (Finset (Fin N))),
    MeasurableSet {u : ℝ | sel d f n free u = A}

end GreedyReusableNet


