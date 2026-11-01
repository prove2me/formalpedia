-- Prove2me | Definitions.Def_DecQueueLearning_TieRules
-- name    : DecQueueLearning_TieRules
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:31.327179+00:00
-- url     : https://prove2.me/theorems/b00cb9c9-51d5-446c-b851-937240a9dd51
-- title:
--   Tie-breaking rules of queues and servers
-- statement:
--   A **tie rule** pair consists of
--   1. for each queue $i$ and slot $t$, a choice $j^\star=\mathrm{argmax}_{i,t}(f)$ of a maximizer of any vector $f\in\mathbb R^{K}$ (used for $j^\star\in\arg\max_j\, w_{i,j}-p_{i,j}(t-1)$ in DAM.CONVERGE);
--   2. for each slot $t$ and server $j$, a selection rule that, given the set $R$ of queues requesting $j$ and their bids $b$, returns a requester of maximal bid, and returns $\bot$ exactly when $R=\emptyset$.
--
--   Both rules are required to be measurable in the real-valued data. The paper breaks ties arbitrarily (footnote 2, p. 7); every theorem of the mission holds for all tie rules.
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, p. 7, footnote 2; Algorithm 2, line 6, p. 11

import Mathlib

namespace DecQueueLearning

/-- **Tie-breaking rules**, arXiv:2206.03324v3, p. 7 (footnote 2: "Ties are assumed to be broken
arbitrarily") and Algorithm 2, line 6, p. 11.

* `argmax i t f` is the server `j⋆ ∈ arg maxⱼ f j` that queue `i` picks at time slot `t`;
* `serve t j R b` is the queue `I(j, t)` that server `j` selects at time slot `t` when the set of
  queues requesting it is `R` and the bids are `b`: a requester with the highest bid, and `none`
  (the paper's `⊥`) exactly when there is no request.

**Formalization Note** Every statement of the mission quantifies over all such rules; both may
depend on the queue or server and on the time slot, and they are required to be measurable in the
real-valued data so that the queue lengths are random variables. -/
structure TieRules (N K : ℕ) where
  argmax : Fin N → ℕ → (Fin K → ℝ) → Fin K
  argmax_spec : ∀ i t (f : Fin K → ℝ) j, f j ≤ f (argmax i t f)
  argmax_measurable : ∀ i t, Measurable (argmax i t)
  serve : ℕ → Fin K → Finset (Fin N) → (Fin N → ℝ) → Option (Fin N)
  serve_eq_none : ∀ t j (R : Finset (Fin N)) (b : Fin N → ℝ), serve t j R b = none ↔ R = ∅
  serve_spec : ∀ t j (R : Finset (Fin N)) (b : Fin N → ℝ) i, serve t j R b = some i → i ∈ R ∧ ∀ i' ∈ R, b i' ≤ b i
  serve_measurable : ∀ t j R i, MeasurableSet {b | serve t j R b = some i}

end DecQueueLearning


