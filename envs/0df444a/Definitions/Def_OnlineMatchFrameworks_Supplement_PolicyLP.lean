-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_PolicyLP
-- name    : OnlineMatchFrameworks_Supplement_PolicyLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:18:54.859997+00:00
-- url     : https://prove2.me/theorems/7b6d2ace-6f67-5e43-9379-84c5ac1f1e7e
-- title:
--   Linear program (2) over policies and $\mathrm{OPT}_{\mathrm{LPP}}(G)$
-- statement:
--   Let $\mathcal P$ be the set of duplicate-free lists of items, the empty list included. Linear program (2) is
--
--   $$
--   \mathrm{OPT}_{\mathrm{LPP}}(G)=\max\ \sum_{v\in V}\sum_{\pi\in\mathcal P}x_v(\pi)\sum_{u\in U}p_{uv}(\pi)\,w_{uv}
--   $$
--
--   subject to
--
--   1. $\sum_v\sum_\pi x_v(\pi)p_{uv}(\pi)\le1$ for every item $u$ (2a);
--   2. $\sum_\pi x_v(\pi)=q_v$ for every type $v$ (2b);
--   3. $x_v(\pi)\ge0$ (2c).
--
--   The variable $x_v(\pi)$ is the expected number of times $\pi$ is applied to an arrival of type $v$. The program is the benchmark through which the algorithms for prophet and IID arrivals are analysed.
--
--   **Formalization Note** The real supremum is a maximum: the point with all mass on the empty list is feasible and $0\le x_v(\pi)\le q_v$.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §4.2, LP (2), pp.16–17

import Definitions.Def_OnlineMatchFrameworks_Supplement_Prophet

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

namespace ProphetInstance

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]

/-- **The objective of LP (2).** arXiv:1907.03963v6, (2), p.16:
`∑_{v ∈ V} ∑_{π ∈ 𝒫} x_v(π) ∑_{u ∈ U} p_{uv}(π) w_{uv}`.

**Formalization Note.** `𝒫` is the published `Policy U`: duplicate-free lists, the empty list included. -/
def policyObjective (G : ProphetInstance U V) (x : V → OnlineMatchFrameworks.Policy U → ℝ) : ℝ :=
  ∑ v, ∑ l : OnlineMatchFrameworks.Policy U, x v l * ∑ u, G.policyMatchProb v l.1 u * G.w u v

/-- **The feasible set of LP (2).** arXiv:1907.03963v6, (2a)–(2c), p.17. -/
structure IsPolicyFeasible (G : ProphetInstance U V)
    (x : V → OnlineMatchFrameworks.Policy U → ℝ) : Prop where
  /-- (2a) -/
  item_le_one : ∀ u, ∑ v, ∑ l : OnlineMatchFrameworks.Policy U, x v l * G.policyMatchProb v l.1 u ≤ 1
  /-- (2b) -/
  type_total : ∀ v, ∑ l : OnlineMatchFrameworks.Policy U, x v l = G.expectedArrivals v
  /-- (2c) -/
  nonneg : ∀ v l, 0 ≤ x v l

/-- **`OPT_LPP(G)`**, "the true optimal objective value" of LP (2). arXiv:1907.03963v6, p.16.

**Formalization Note.** The feasible set contains the point with all mass on the empty list and is
bounded, since `0 ≤ x_v(π) ≤ q_v`; so the real supremum is the LP optimum. -/
noncomputable def OPTLPP (G : ProphetInstance U V) : ℝ :=
  sSup (G.policyObjective '' {x | G.IsPolicyFeasible x})

end ProphetInstance

end OnlineMatchFrameworks.Supplement


