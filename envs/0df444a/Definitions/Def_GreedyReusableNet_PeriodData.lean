-- Prove2me | Definitions.Def_GreedyReusableNet_PeriodData
-- name    : GreedyReusableNet_PeriodData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:03.671502+00:00
-- url     : https://prove2.me/theorems/2fd9d786-5406-44e4-9c28-84985f138828
-- title:
--   One period's data $(\mathcal B_t,\mathscr A_t,\text{activation law},r_t)$
-- statement:
--   In each period $t$ of the online problem the following is revealed: a **basis** $\mathcal B_t$ of bundles, each bundle being a subset of the arms $[N]$; a family $\mathscr A_t$ of **action sets**, each a set of bundles; an **activation law**, which for every action set $\mathcal A$ and counting vector $n$ is a probability distribution over the subsets $\mathcal A_{\mathrm{act}}$ of activated bundles; and a **reward function** $r_t(B;n(B))\in\mathbb R$ collected when bundle $B$ is activated and its arms have been activated $n(B)=(n_i)_{i\in B}$ times before.
--
--   This is step 2 of the data generation procedure (Algorithm 1) of Simchi-Levi, Zheng and Zhu: everything the decision maker learns at the start of period $t$, apart from the blocking-time laws, which do not depend on $t$.
--
--   **Formalization Note** Arms are $\{0,\dots,N-1\}$. The activation law is data and the marginal activation probability $\mathbb P_t(B\mid\mathcal A,n(B))$ is defined from it (`prob`). Rewards and the activation law take the whole counting vector; their dependence on $n(B)$ only follows from the decaying assumptions as encoded. No sign condition is imposed on rewards.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Algorithm 1 step 2, p.8; pp.9–10

import Mathlib

namespace GreedyReusableNet

/-- **The data revealed in one period** (Simchi-Levi, Zheng & Zhu, *On Greedy-like Policies in
Online Matching with Reusable Network Resources and Decaying Rewards*, SSRN 3981123, §2.1,
Algorithm 1 step 2, p.8, and pp.9–10).

In period `t` the following is revealed: the basis `𝓑_t` of bundles (`bundles`), the family `𝒜_t`
of action sets (`actions`), the activation mechanism and the reward function `r_t(B; n(B))`
(`reward`).

**Formalization Note**
* Arms are `Fin N` (the paper's `[N] = {1, …, N}` shifted by one); a bundle is a `Finset (Fin N)`
  and an action set is a `Finset` of bundles.
* `act A n` is the **activation law** of the period: the probability distribution of the
  activated subset `𝒜_{t,act}` when the action set `A` is taken with counting vector `n`
  ("the nature draws an independent sample `𝒜^π_{t,act} ⊂ 𝒜^π_t` from an activation probability
  distribution determined by `(t, 𝒜^π_t, n^π_t)`", p.9). The marginal activation probability
  `ℙ_t(B | A, n(B))` of (1) is *defined* from it (`GreedyReusableNet.prob`), not given separately.
* Counting vectors are whole vectors `n : Fin N → ℕ`; that `r_t(B; ·)` and `ℙ_t(B | A, ·)` depend
  only on `n(B) = (n_i)_{i ∈ B}` follows from Assumption 5.1/5.2 as encoded (conditions on the
  coordinates in `B` only).
* No sign condition is imposed on rewards (the paper states none). -/
structure PeriodData (N : ℕ) where
  /-- the basis `𝓑_t` of bundles -/
  bundles : Finset (Finset (Fin N))
  /-- the family `𝒜_t` of action sets -/
  actions : Finset (Finset (Finset (Fin N)))
  /-- the activation law: distribution of the activated subset of the action set `A` at counts `n` -/
  act : Finset (Finset (Fin N)) → (Fin N → ℕ) → PMF (Finset (Finset (Fin N)))
  /-- the reward `r_t(B; n(B))` collected when bundle `B` is activated at counts `n` -/
  reward : Finset (Fin N) → (Fin N → ℕ) → ℝ

end GreedyReusableNet


