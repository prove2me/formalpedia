-- Prove2me | Definitions.Def_CompetingAgents_quantile
-- name    : CompetingAgents_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:53.017854+00:00
-- url     : https://prove2.me/theorems/3d41a42c-eed2-4c7b-8448-b6c1a6328a24
-- title:
--   Lower quantile $q(G)=\inf\{r: p\le G(r)\}$ and the empirical distribution function
-- statement:
--   For a level $p$ and a function $G:\mathbb R\to\mathbb R$ (a distribution function), the **lower $p$-th quantile** is
--
--   $$q_p(G)=\inf\{r\in\mathbb R : p\le G(r)\}.$$
--
--   For $n$ real observations $x_1,\dots,x_n$, the **empirical distribution function** is
--
--   $$F_n(r)=\frac{\#\{j : x_j\le r\}}{n}.$$
--
--   The population threshold $q(P(\beta,s))$, the sample threshold $q(P^n(\beta,s))$ and the sample quantile $\hat\theta_p$ of Theorem 17 are all built from these two objects.
--
--   **Formalization Note** The infimum is a real `sInf`, which is $0$ on an empty or unbounded-below set. Every statement uses $0<p<1$ and applies $q_p$ to the distribution function of a probability measure or to $F_n$ with $n\ge1$, where the set is nonempty and bounded below. With $n=0$, $F_0\equiv0$ (Lean's $0/0=0$) and the quantile is the junk value $0$; the statements that can meet this case are trivially true there.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Theorem 17, p.30 (quantile of $F$ and of $F_n$); §2.1, p.5 ($q$-th quantile); §4, p.9 ($P^n$)

import Mathlib

namespace CompetingAgents

/-- The lower `p`-th quantile of a distribution function `G : ℝ → ℝ`,
`q(G) = inf {r : p ≤ G r}`: the convention of Shao, *Mathematical Statistics* (2003), §5.3, which
Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Theorem 17, p.30, cites
for its sample quantiles, and the `q`-th quantile `q(P)` of §2.1, p.5.

**Formalization Note.** `sInf` of a real set is `0` when the set is empty or unbounded below. Every
statement of this mission applies `quantile` with `0 < p < 1` either to the distribution function of
a probability measure (the set is then nonempty and bounded below) or to an empirical distribution
function with at least one observation (the set is then nonempty and bounded below). With zero
observations the empirical distribution function is identically `0` and the quantile is the junk
value `0`; the statements that can meet this case say so. -/
noncomputable def quantile (p : ℝ) (G : ℝ → ℝ) : ℝ :=
  sInf {r : ℝ | p ≤ G r}

/-- The empirical distribution function of `n` real observations `x 0, …, x (n-1)`:
`F_n(r) = #{j : x j ≤ r} / n` (Sahoo, Wager, arXiv:2204.01884v5, Theorem 17, p.30, "the `p`-th
quantile of `F_n`"; and `Pⁿ(β, s)`, §4, p.9).

**Formalization Note.** At `n = 0` Lean's division gives `0 / 0 = 0`, so `F_0 ≡ 0`. -/
noncomputable def empiricalCDF {n : ℕ} (x : Fin n → ℝ) (r : ℝ) : ℝ :=
  ((Finset.univ.filter fun j => x j ≤ r).card : ℝ) / n

end CompetingAgents


