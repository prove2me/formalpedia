-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_IsWeightOrder
-- name    : OfflineStochMatching_UnitPatience_IsWeightOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:49.409979+00:00
-- url     : https://prove2.me/theorems/71e8f471-f605-4c51-b4d4-fd02aca88a8c
-- title:
--   Probing order of decreasing weight on each star of $V_2$
-- statement:
--   A family of lists $\sigma=(\sigma_v)_{v\in V}$ of edges is a **weight order on $V_2$** if, for every $v\in V_2$, $\sigma_v$ lists each edge of $\delta(v)$ exactly once and in weight-nonincreasing order, $w_{e_1}\ge w_{e_2}\ge\cdots\ge w_{e_k}$. It is the order in which the algorithm of Section 4 probes the star of $v$.
--
--   **Formalization Note** Ties between equal weights may be broken arbitrarily: every such list is allowed. Outside $V_2$ the lists are unconstrained and unused.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §4, p. 16 (probe the edges e ∈ δ(v) in decreasing order of weight; Lemma 7: w1 ≥ w2 ≥ ··· ≥ wk)

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_incident

namespace OfflineStochMatching.UnitPatience

/-- **Probing order of decreasing weight at each vertex of `V2`.**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §4, p. 16: "For each vertex
`v ∈ V2`, we probe the edges `e ∈ δ(v)` in decreasing order of weight"; Lemma 7, p. 16: "Label
the edges of `δ(v)` from `1` to `k := |δ(v)|` such that `w1 ≥ w2 ≥ ··· ≥ wk`."

`IsWeightOrder G V2 σ` says that for every `v ∈ V2` the list `σ v` enumerates `δ(v)` exactly
once each, in weight-nonincreasing order.

**Formalization Note.** Ties between equal weights may be broken in any way: every such list is
allowed. Outside `V2` the lists are unconstrained and unused. -/
def IsWeightOrder {V E : Type*} [Fintype E] [DecidableEq V]
    (G : StochGraph V E) (V2 : Finset V) (σ : V → List E) : Prop :=
  ∀ v ∈ V2, (σ v).Nodup ∧ (∀ e, e ∈ σ v ↔ e ∈ incident G v) ∧
    (σ v).Pairwise (fun e e' => G.w e' ≤ G.w e)

end OfflineStochMatching.UnitPatience


