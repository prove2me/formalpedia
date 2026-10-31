-- Prove2me | Definitions.Def_CentralityGame_hittingTime
-- name    : CentralityGame_hittingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:32.453486+00:00
-- url     : https://prove2.me/theorems/2b70dbc9-e182-42a6-a5e4-18bed56a113a
-- title:
--   Expected hitting time $\tau^i_j$
-- statement:
--   Let $(V_t)_{t\ge 0}$ be the Markov chain with transition matrix $P=\beta R+(1-\beta)\mathbf 1\eta^\top$. Let $T_i=\min\{t\ge 0:V_t=i\}$ be the hitting time in $i$. The **expected hitting time** of $i$ from $j$ is
--
--   $$
--   \tau^i_j=\mathbb E[T_i: V_0=j].
--   $$
--
--   In particular $\tau^i_i=0$. These quantities carry the whole analysis: Lemma 1 expresses PageRank through them, and Proposition 2 reads best responses from them.
--
--   **Formalization Note** The expectation is the tail sum $\sum_{t\ge 0}\mathbb P_j(T_i>t)$, using the published definition `MarkovMixing.expSetHitTime` at the set $\{i\}$. It is not defined as the solution of the system (4); the two are linked by `CentralityGame.eq_4`.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, p.7

import Mathlib
import Definitions.Def_mm_path
import Definitions.Def_CentralityGame_chain

namespace CentralityGame

/-- The **expected hitting time** `τ^i_j = E[T_i : V_0 = j]` of (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, p.7),
where `T_i = min {t ≥ 0 : V_t = i}` and `(V_t)` is the chain with transition matrix `P` of (3).

**Formalization Note** This is the published `MarkovMixing.expSetHitTime` at the singleton `{i}`,
the tail sum `∑_{t ≥ 0} P_j{T_i > t}`, with the time counted from `0` so that `τ^i_i = 0`. It is the
probabilistic quantity and not the solution of (4); the link is `CentralityGame.eq_4`. The sum
is `0` by convention if the tails are not summable, which does not happen for a positive `η`
(each step reaches `i` with probability at least `(1 - β) η_i > 0`). -/
noncomputable def hittingTime {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V) (β : ℝ)
    (η : V → ℝ) (i j : V) : ℝ :=
  MarkovMixing.expSetHitTime (chain N β η) j {i}

end CentralityGame


