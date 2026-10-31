-- Prove2me | Definitions.Def_QuantileMDP_opt
-- name    : QuantileMDP_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:24.745482+00:00
-- url     : https://prove2.me/theorems/3badbebc-3330-4e9a-9d13-0d8f7fb3faed
-- title:
--   The problem $\mathrm{OPT}$: $\max_q\min_{i:q_i\neq1}g_i(q_i)$ over $q\in[0,1]^n$ (corrected: strict budget $\sum_i p_iq_i<\tau$ or $=0$)
-- statement:
--   Let $\iota=\{1,\dots,n\}$ be a finite index set, $p\in\mathbb R^\iota$ a weight vector, $g_i:\mathbb R\to[-\infty,\infty]$ a function for each $i$, and $\tau\in\mathbb R$. A vector $q\in\mathbb R^\iota$ is **feasible** if
--
--   1. $q_i\in[0,1]$ for every $i$, and
--   2. $\sum_{i}p_iq_i<\tau$ or $\sum_i p_iq_i=0$.
--
--   The value of the problem is
--
--   $$
--   \mathrm{OPT}(p,g,\tau)=\sup_{q\ \text{feasible}}\ \min_{i\in\{i\,:\,q_i\neq1\}} g_i(q_i),
--   $$
--
--   with the minimum over an empty set equal to $+\infty$ and the supremum over an empty set equal to $-\infty$.
--
--   This is the common form of the optimization problems (8) of Theorem 1, (9) of Lemma 2 and (10) of §4.1: with $p_i$ the probability of the $i$-th branch and $g_i(q)$ the $q$-quantile of the $i$-th branch, it computes the $\tau$-quantile of the mixture.
--
--   **Formalization Note** The paper's budget is $\sum_i p_iq_i\le\tau$. As printed, the problem overestimates the quantile at boundary levels: for one step from $s_1$ to two equally likely states with rewards $0$ and $10$ and $\tau=1/2$, the vector $q=(1,0)$ costs $1/2\le1/2$ and leaves only the reward $10$ in the minimum, while the true $1/2$-quantile is $0$. The budget is therefore strict, except that a budget of exactly $0$ is allowed, which leaves $\tau=0$ unchanged. Values are in `EReal`. `opt` is a supremum; the page's OPT is a maximum, so the predicate `OptAttained p g τ` says that some feasible $q$ reaches `opt p g τ`, and the theorems that compute OPT assert it.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, Theorem 1 (8), p.11; Lemma 2 (9), p.12; §4.1 (10), p.16

import Mathlib

namespace QuantileMDP

/-- The feasible set of the problem `OPT` ((8), (9), (10)), with the corrected budget: vectors
`q ∈ [0,1]^ι` with `∑ i, p i * q i < τ` or `∑ i, p i * q i = 0`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, Theorem 1 (8),
p.11; Lemma 2 (9), p.12; §4.1 (10), p.16.

**Formalization Note** The printed budget is `∑ p_i q_i ≤ τ`. It is false at boundary levels
(one step to two equally likely states with rewards `0` and `10`, `τ = 1/2`: the printed
problem gives `10`, the true quantile is `0`), so the budget is strict, except that a budget of
exactly `0` is allowed, which leaves `τ = 0` unchanged. -/
def Feasible {ι : Type*} [Fintype ι] (p : ι → ℝ) (τ : ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, q i ∈ Set.Icc (0 : ℝ) 1) ∧ (∑ i, p i * q i < τ ∨ ∑ i, p i * q i = 0)}

/-- The optimization problem `OPT` of (8)–(10) with the corrected budget (`Feasible`):
`max_q min_{i ∈ {i | q_i ≠ 1}} g_i(q_i)` over feasible `q`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, Theorem 1 (8),
p.11; Lemma 2 (9), p.12; §4.1 (10), p.16.

**Formalization Note** Values in `EReal`; `max` and `min` are the complete-lattice `⨆` and `⨅`.
The minimum over `{i | q_i ≠ 1}` is `⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)`. When `∑ p_i = 1`, every
feasible `q` has some `q_i ≠ 1`, so the minimum is never over an empty set. -/
noncomputable def opt {ι : Type*} [Fintype ι] (p : ι → ℝ) (g : ι → ℝ → EReal) (τ : ℝ) : EReal :=
  ⨆ q ∈ Feasible p τ, ⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)

/-- The `max` of `OPT` is attained: some feasible `q` has objective value `opt p g τ`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, Theorem 1 (8),
p.11; Lemma 2 (9), p.12.

**Formalization Note** `opt` is a supremum, the page's `OPT` a maximum; the theorems that assert
a value of `OPT` assert this as well. -/
def OptAttained {ι : Type*} [Fintype ι] (p : ι → ℝ) (g : ι → ℝ → EReal) (τ : ℝ) : Prop :=
  ∃ q ∈ Feasible p τ, (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = opt p g τ

end QuantileMDP


