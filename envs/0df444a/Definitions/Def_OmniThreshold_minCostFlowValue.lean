-- Prove2me | Definitions.Def_OmniThreshold_minCostFlowValue
-- name    : OmniThreshold_minCostFlowValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:43.454218+00:00
-- url     : https://prove2.me/theorems/f167cf5e-4b70-4da1-8875-54d8a99f185b
-- title:
--   Optimal value of a min-cost flow problem as a function of the source supplies
-- statement:
--   Let $(V,E,\mathrm{tail},\mathrm{head},w,u)$ be a flow network, let $\mathrm{src}:\iota\to V$ list the source nodes, let $t\in V$ be the sink, and let $b\in\mathbb N^{\iota}$ be the supplies. A flow $\xi\in\mathbb R^E$ is **feasible** if $0\le\xi_e\le u_e$ on every arc and its net out-flow at every node $v$ is
--   $$
--   \sum_{e:\,\mathrm{tail}(e)=v}\xi_e-\sum_{e:\,\mathrm{head}(e)=v}\xi_e
--   =\sum_{k:\,\mathrm{src}(k)=v}b_k-[v=t]\sum_{k}b_k ,
--   $$
--   that is, each source ships out its supply, the sink absorbs the total supply, and every other node conserves flow. The **min-cost flow value** is
--   $$
--   V(b)=\inf\Bigl\{\sum_{e\in E}w_e\,\xi_e:\ \xi\ \text{feasible}\Bigr\}\in\mathbb R\cup\{+\infty\},
--   $$
--   with $V(b)=+\infty$ when no feasible flow exists.
--
--   This is "the objective value of a minimum cost feasible flow as a function of the supplies at the source nodes" of Lemma 1, the function $V(s_1,\dots,s_n)$ of its proof in Appendix B.
--
--   **Formalization Note** The value lies in `WithTop ℝ`. Flows are real; when the feasible set is nonempty it is a polytope, so the infimum is a minimum. Feasibility is the published Murota definition `FeasibleFlowMCFP0` with lower capacity $0$ and upper capacity $u$; the boundary there is out-flow minus in-flow.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, Lemma 1, p.9; proof of Lemma 1, Appendix B, p.28

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
import Definitions.Def_OmniThreshold_FlowNetwork

namespace OmniThreshold

open DiscreteConvex.NetworkFlows

open Classical in
/-- The **optimal value of a minimum-cost, single-commodity flow problem with multiple sources and
one sink, as a function of the supplies at the source nodes** (Jia, Karp, Ravi & Tayur, SSRN
3932692, Lemma 1, p.9, and its proof, Appendix B, p.28: "let `V(s) = V(s₁, …, sₙ)` be the objective
value of the minimum cost flow in a fixed network as a function of `s`").

The source nodes are `src k` (`k : ι`) with supplies `b k ∈ ℕ`, and `t` is the sink, whose demand
is the total supply `∑ₖ b k`; every other node has zero net flow. A flow `ξ : E → ℝ` is feasible if
`0 ≤ ξ e ≤ cap e` on every arc and its boundary (out-flow minus in-flow) at node `v` is
`∑_{k : src k = v} b k − [v = t] ∑ₖ b k`. The value is the infimum of `∑ₑ cost e · ξ e` over the
feasible flows, and `⊤` if there is none.

**Formalization Note** Flows are real; the feasible set is a polytope (bounded by the
capacities), so when it is nonempty the infimum is a minimum. Feasibility is the published
`DiscreteConvex.NetworkFlows.FeasibleFlowMCFP0` (Murota's (9.12)–(9.13)) with lower capacity `0`
and upper capacity `cap`. The supply at a node sums over the sources mapped to it, which is `b k`
at `src k` when `src` is injective and the sink is not a source, as Lemma 1 assumes. -/
noncomputable def minCostFlowValue {V E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq V]
    (G : FlowNetwork V E) (src : ι → V) (t : V) (b : ι → ℕ) : WithTop ℝ :=
  let x : V → ℝ := fun v =>
    (∑ k ∈ Finset.univ.filter (fun k => src k = v), (b k : ℝ)) -
      (if v = t then ∑ k, (b k : ℝ) else 0)
  let feas : Set (E → ℝ) :=
    {ξ | FeasibleFlowMCFP0 G.tail G.head (fun e => ((G.cap e : ℝ) : WithTop ℝ))
      (fun _ => ((0 : ℝ) : WithBot ℝ)) x ξ}
  if feas.Nonempty then
    ((sInf ((fun ξ : E → ℝ => ∑ e, G.cost e * ξ e) '' feas) : ℝ) : WithTop ℝ)
  else ⊤

end OmniThreshold


