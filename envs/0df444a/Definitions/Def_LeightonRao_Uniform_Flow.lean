-- Prove2me | Definitions.Def_LeightonRao_Uniform_Flow
-- name    : LeightonRao_Uniform_Flow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:18.496989+00:00
-- url     : https://prove2.me/theorems/9de96f74-c134-46ef-918f-87b34d0912a0
-- title:
--   §1.2, §1.4, pp. 789–791 — concurrent multicommodity flow, max-flow f, uniform demands
-- statement:
--   A multicommodity flow problem on a network has one commodity for every ordered pair $(s,t)$ of distinct nodes, with demand $D(s,t)\ge0$. A **concurrent flow of value $\lambda$** consists of nonnegative arc flows $f_{st}(i\to j)$, one for each commodity and each ordered pair of nodes, such that
--
--   1. for every commodity $(s,t)$ with $s\ne t$ and every node $v$, the net outflow at $v$ equals $\lambda D(s,t)$ if $v=s$, $-\lambda D(s,t)$ if $v=t$, and $0$ otherwise;
--   2. the diagonal commodities $(s,s)$ carry no flow;
--   3. on every pair $\{i,j\}$, the total flow of all commodities in both directions is at most the capacity:
--   $$\sum_{s,t}\bigl(f_{st}(i\to j)+f_{st}(j\to i)\bigr)\le C(i,j).$$
--
--   The **max-flow** (concurrent max-flow) is the largest $f$ such that $fD_i$ units of every commodity can be routed simultaneously:
--   $$f=\sup\{\lambda\ge0:\ \text{a concurrent flow of value }\lambda\text{ exists}\}.$$
--   In a **uniform multicommodity flow problem** (UMFP) every unordered pair of nodes has demand one; following footnote 2 of the paper this is encoded as two ordered commodities with demand $\tfrac12$ each.
--
--   **Formalization Note** The flow is in arc form, with both directions of an undirected edge sharing its capacity (p. 789). The max-flow is a real supremum. Its set contains $0$, and when $n\ge2$ and some demand is positive it is bounded above by any cut separating that commodity, so the supremum is the paper's maximum; every theorem about it assumes $n\ge2$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 788–789 (§1.2, concurrent max-flow), p. 791 (§1.4, UMFP and footnote 2)

import Definitions.Def_LeightonRao_Uniform_Network

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Concurrent arc flow for ordered source-sink pairs. Both directions of each undirected
edge share one capacity. The diagonal commodities carry no flow. -/
def IsConcurrentFlow (N : Network V) (D : V → V → ℝ)
    (f : V → V → V → V → ℝ) (lam : ℝ) : Prop :=
  (∀ s t i j, 0 ≤ f s t i j) ∧
  (∀ s t, s ≠ t → ∀ v,
    (∑ j, f s t v j) - (∑ j, f s t j v) =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
  (∀ s i j, f s s i j = 0) ∧
  (∀ i j, ∑ s, ∑ t, (f s t i j + f s t j i) ≤ N.C i j)

/-- The concurrent max-flow value. Under at least two vertices and positive demands, a
proper cut bounds its nonnegative feasible set above, while zero is feasible. -/
noncomputable def maxFlow (N : Network V) (D : V → V → ℝ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N D f lam}

/-- Two ordered commodities of demand `1/2` represent each unordered unit-demand pair. -/
noncomputable def uniformDemand (s t : V) : ℝ := if s = t then 0 else 1 / 2

end LeightonRao.Uniform


