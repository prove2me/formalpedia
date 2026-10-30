-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_StochGraph
-- name    : OfflineStochMatching_UnitPatience_StochGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:21.459762+00:00
-- url     : https://prove2.me/theorems/3bd86e25-d9db-4e14-922c-13a28f60e4ac
-- title:
--   Weighted stochastic graph with patience parameters $t_v\in\mathbb N\cup\{\infty\}$
-- statement:
--   A **weighted stochastic graph** $G=(V,E)$ consists of finite sets of vertices $V$ and edges $E$, where every edge $e$ has two distinct endpoints, a weight $w_e\in\mathbb R$ and a probability $p_e\in[0,1]$ of being *active*, and every vertex $v$ has a **patience** $t_v\in\mathbb N\cup\{\infty\}$: at most $t_v$ edges incident to $v$ may be probed.
--
--   Edges are active independently. An edge whose endpoints are unmatched (and have patience left) may be probed; if it is active it is irrevocably added to the matching. This is the input of the offline stochastic matching problem with patience constraints, the object of every statement in this mission.
--
--   **Formalization Note** The edge type carries its own two endpoint maps, so parallel edges are allowed and every simple graph is an instance; the orientation of the maps has no meaning. Patience is an element of `ℕ∞`, with $\top$ the paper's $\infty$. No sign condition is imposed on the weights.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, pp. 1–2 (active edges, patience parameters, t_v = ∞ allowed); §2, p. 6 (weighted stochastic graph G = (V, E), w_e, p_e, t_v)

import Mathlib

namespace OfflineStochMatching.UnitPatience

/-- **Weighted stochastic graph with patience parameters.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, p. 1: "each edge `e` is
*active* independently according to a known probability `p_e`"; §1, p. 2: "an integral *patience
parameter* `t_v` for each vertex `v` … we allow patience parameters to be `∞`"; §2, p. 6: "The
weighted stochastic graph is denoted by `G = (V, E)`, with the weight and probability of being
active being denoted by `w_e` and `p_e`, respectively, for each edge `e ∈ E`. The patience
parameter is denoted by `t_v` for each vertex `v ∈ V`."

An instance on a vertex type `V` and an edge type `E`: every edge `e` has two distinct endpoints
`src e ≠ dst e`, a real weight `w e`, an activation probability `p e ∈ [0, 1]`, and every vertex
`v` has a patience `t v ∈ ℕ ∪ {∞}`.

**Formalization Note.** The edge type carries its own endpoint maps, so parallel edges are
allowed (every simple graph is an instance); the orientation `src`/`dst` carries no meaning.
Patience lives in `ℕ∞`, with `⊤` the paper's `∞`. No sign condition is imposed on the weights. -/
structure StochGraph (V E : Type*) where
  /-- one endpoint of each edge -/
  src : E → V
  /-- the other endpoint of each edge -/
  dst : E → V
  /-- edges are not loops -/
  src_ne_dst : ∀ e, src e ≠ dst e
  /-- the weight `w_e` -/
  w : E → ℝ
  /-- the activation probability `p_e` -/
  p : E → ℝ
  p_nonneg : ∀ e, 0 ≤ p e
  p_le_one : ∀ e, p e ≤ 1
  /-- the patience `t_v ∈ ℕ ∪ {∞}` -/
  t : V → ℕ∞

end OfflineStochMatching.UnitPatience


