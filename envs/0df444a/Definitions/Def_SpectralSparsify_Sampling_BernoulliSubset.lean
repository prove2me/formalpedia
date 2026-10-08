-- Prove2me | Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
-- name    : SpectralSparsify_Sampling_BernoulliSubset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:23.626066+00:00
-- url     : https://prove2.me/theorems/79716507-1370-458c-adbb-4900139010f5
-- title:
--   Independent Bernoulli selection of a subset of a finite set: outcome probability, Pr and E as finite sums
-- statement:
--   Let $E$ be a finite set and $p:E\to\mathbb R$. Keep each $e\in E$ independently with probability $p_e$. The outcome is the set $T\subseteq E$ of kept elements, and it has probability
--   $$\Pr[T]=\prod_{e\in T}p_e\prod_{e\in E\setminus T}(1-p_e).$$
--   For an event $P$ (a property of $T$) and a real random variable $X$ (a function of $T$),
--   $$\Pr[P]=\sum_{T\subseteq E,\ P(T)}\Pr[T],\qquad \mathbf E[X]=\sum_{T\subseteq E}\Pr[T]\,X(T).$$
--
--   This is the probability model of §6: every edge of the graph is put in the sampled graph independently with its own probability, and the random variables of Theorem 6.8 are independent two-valued variables of the same kind.
--
--   **Formalization Note** The law is meaningful when $0\le p_e\le 1$; every statement of the mission applies it to such probabilities (the probabilities (4) lie in $(0,1]$ when $\Upsilon>0$ and the degrees are positive; Theorem 6.8 assumes $p_i\in[0,1]$). Everything is a finite sum; no measure theory is used.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, §6, p. 7 (independent sampling of edges) and p. 15, Theorem 6.8 (independent variables)

import Mathlib

namespace SpectralSparsify.Sampling

/-- Independent Bernoulli selection of the elements of a finite set `E`: each `e ∈ E` is kept
independently with probability `p e`. The outcome is the set `T ⊆ E` of kept elements, and its
probability is `Pr[T] = ∏_{e ∈ T} p e · ∏_{e ∈ E \ T} (1 - p e)`. -/
def outcomeProb {α : Type*} [DecidableEq α] (E : Finset α) (p : α → ℝ) (T : Finset α) : ℝ :=
  (∏ e ∈ T, p e) * ∏ e ∈ E \ T, (1 - p e)

open scoped Classical in
/-- The probability `Pr[P] = ∑_{T ⊆ E, P T} Pr[T]` of an event `P` (a property of the outcome `T`)
under independent Bernoulli selection from `E` with probabilities `p`. -/
noncomputable def prob {α : Type*} [DecidableEq α] (E : Finset α) (p : α → ℝ)
    (P : Finset α → Prop) : ℝ :=
  ∑ T ∈ E.powerset, if P T then outcomeProb E p T else 0

/-- The expectation `E[X] = ∑_{T ⊆ E} Pr[T] · X(T)` of a real random variable `X` (a function of
the outcome `T`) under independent Bernoulli selection from `E` with probabilities `p`. -/
noncomputable def expect {α : Type*} [DecidableEq α] (E : Finset α) (p : α → ℝ)
    (X : Finset α → ℝ) : ℝ :=
  ∑ T ∈ E.powerset, outcomeProb E p T * X T

end SpectralSparsify.Sampling


