-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_Prophet
-- name    : OnlineMatchFrameworks_Supplement_Prophet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:18:14.919747+00:00
-- url     : https://prove2.me/theorems/61709e7f-ce29-5431-b891-2a499d020e80
-- title:
--   Prophet arrivals and the clairvoyant benchmark $\mathrm{OPT}(G)$
-- statement:
--   In the **prophet arrival model** the online vertices have types in a finite set $V$, the horizon $T$ is known, and the arrival at time $t$ has type $v$ with probability $q_{tv}$, independently over $t$, where $q_{tv}\ge0$ and $\sum_vq_{tv}=1$. Write $q_v=\sum_tq_{tv}$. Arrivals are **IID** if $q_{tv}$ does not depend on $t$.
--
--   The **clairvoyant** knows the realized types $\sigma=(\sigma_1,\dots,\sigma_T)$ and neither the edge coins nor the patience. It is an adaptive sequential probing strategy on the $T$ arrivals that finishes one arrival before the next. Its benchmark is
--
--   $$
--   \mathrm{OPT}(G)=\sum_{\sigma\in V^T}\Bigl(\prod_{t}q_{t,\sigma_t}\Bigr)\ \sup_{\mathcal T}\ \mathrm{value}_\sigma(\mathcal T),
--   $$
--
--   the supremum over the strategies $\mathcal T$ in which each item is matched at most once and each arrival is served at most once. Competitive ratios under stochastic arrivals are measured against this value.
--
--   **Formalization Note** Strategies are the published decision trees, with time slots as customers. The tree may choose the order of the slots.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §3, pp.11–12; §4.2, p.16; §4.3, p.20

import Definitions.Def_OnlineMatchFrameworks_Supplement_EdgeWeighted
import Definitions.Def_OnlineMatchFrameworks_Offline

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

/-- **An instance with prophet arrivals.** arXiv:1907.03963v6, §3, p.11, and §4.2, p.16: `V` is a finite set
of types, the horizon `horizon = T` is known, and the arrival at time `t` has type `v` with probability
`q t v`, independently of the other arrivals.

**Formalization Note.** Times are `Fin T`, so the paper's `t = 1,…,T` is `0,…,T-1`. Weights are edge
weights; vertex weights are the special case in which `w u v` does not depend on `v`. -/
structure ProphetInstance (U V : Type*) [Fintype V] extends EdgeInstance U V where
  /-- The horizon `T`. -/
  horizon : ℕ
  /-- `q_{tv}`, the probability that the arrival at time `t` has type `v`. -/
  q : Fin horizon → V → ℝ
  q_nonneg : ∀ t v, 0 ≤ q t v
  q_sum : ∀ t, ∑ v, q t v = 1

namespace ProphetInstance

variable {U V : Type*} [Fintype V]

/-- **`q_v = ∑_t q_{tv}`**, the expected number of arrivals of type `v`. arXiv:1907.03963v6, §4.2, p.16. -/
def expectedArrivals (G : ProphetInstance U V) (v : V) : ℝ :=
  ∑ t, G.q t v

/-- **IID arrivals.** arXiv:1907.03963v6, §4.3, p.20: `q_{1v} = q_{2v} = ⋯ = q_{Tv}` for all types `v`. -/
def IsIID (G : ProphetInstance U V) : Prop :=
  ∀ t t' v, G.q t v = G.q t' v

/-- **Expected reward of an offline strategy on a realized type sequence `σ`.** arXiv:1907.03963v6, §3,
p.12. The strategy is a tree as in `OnlineMatchFrameworks.Strategy`, whose customers are the time slots
`t`; slot `t` carries the type `σ t`, and a match of `u` there earns `w_{u,σ t}`. -/
def clairvoyantValue (G : ProphetInstance U V) (σ : Fin G.horizon → V) :
    OnlineMatchFrameworks.Strategy U (Fin G.horizon) → ℝ
  | .done => 0
  | .visit t l g h =>
      ∑ i : Fin l.length, (G.atType (σ t)).matchProb (σ t) l i *
          (G.w (l.get i) (σ t) + G.clairvoyantValue σ (g (l.get i))) +
        (1 - ∑ i : Fin l.length, (G.atType (σ t)).matchProb (σ t) l i) * G.clairvoyantValue σ h

/-- **The benchmark `OPT(G)` for stochastic arrivals.** arXiv:1907.03963v6, §3, p.12: the expected reward
of the best sequential probing algorithm which knows "the sequence of T types that will be realized",
the expectation being "also over the realizations of the T types".

**Formalization Note.** For each sequence `σ`, of probability `∏_t q_{t,σ t}`, the supremum is over the
valid trees on the items and the time slots. A tree knows `σ` but neither the edge coins nor the
patience, finishes a slot before the next, and may choose the order of the slots adaptively, which only
raises the benchmark. The index type is nonempty and the values are bounded by `∑_t ∑_u w_{u,σ t}`. -/
noncomputable def OPT [Fintype U] [DecidableEq U] (G : ProphetInstance U V) : ℝ :=
  ∑ σ : Fin G.horizon → V, (∏ t, G.q t (σ t)) *
    ⨆ S : {S : OnlineMatchFrameworks.Strategy U (Fin G.horizon) //
        S.ValidFrom Finset.univ Finset.univ}, G.clairvoyantValue σ S.1

end ProphetInstance

end OnlineMatchFrameworks.Supplement


