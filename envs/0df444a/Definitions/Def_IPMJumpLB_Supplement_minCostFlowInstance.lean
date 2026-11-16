-- Prove2me | Definitions.Def_IPMJumpLB_Supplement_minCostFlowInstance
-- name    : IPMJumpLB_Supplement_minCostFlowInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:49:20.666575+00:00
-- url     : https://prove2.me/theorems/3e0f21dc-449d-4ed2-86c4-697c9b2643d0
-- title:
--   The hard min-cost flow instance of Section 3.1
-- statement:
--   For an integer $k$ (the paper takes $k \ge 3$), the **hard instance** of Section 3.1 is the min-cost flow instance $(G, c, d)$ on the vertices $V_k$ and the arcs $E_k$ with
--
--   1. path arcs $e_i^+ = (v_i, v_{i+1})$ and $e_i^- = (v_{i+1}, v_i)$, $0 \le i < k$, each of cost $1$;
--   2. shortcut arcs $(v_0, a_j)$ and $(a_j, v_k)$, $1 \le j \le k^2$, each of cost $k$ (so each shortcut path costs $C_k = 2k$);
--   3. demands
--   $$
--   d_{v_0} = 2k,\qquad d_{v_i} = -1\ (1 \le i < k),\qquad d_{v_k} = -(k+1),\qquad d_{a_j} = 0\ (1 \le j \le k^2).
--   $$
--
--   The demands sum to zero. Viewed as a shortest path problem, the optimum sends one unit from $v_0$ to each of $v_1, \dots, v_{k-1}$ and $k+1$ units to $v_k$ along the forward arcs. This is the instance of Theorem 3.1.
--
--   **Formalization Note** Built on the published `IPMJumpLB.FlowInstance` (tail, head, cost, demand). The demand of $v_i$ is defined as $2k$ if $i = 0$, otherwise $-(k+1)$ if $i = k$, otherwise $-1$; for $k \ge 1$ these are exactly the three cases of the page.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), §3.1, p.6 (instance, Eq. (7) and the demand vector)

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_Supplement_VertexS
import Definitions.Def_IPMJumpLB_Supplement_ArcS

namespace IPMJumpLB

namespace Supplement

/-- The hard min-cost flow instance of Section 3.1
(Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §3.1, p.6), for an integer `k` (the paper takes `k ≥ 3`):

* the main path: for each `0 ≤ i < k`, a forward arc `e⁺ᵢ = (vᵢ, vᵢ₊₁)` and a backward arc
  `e⁻ᵢ = (vᵢ₊₁, vᵢ)`, each of cost `1` (gadget `i`);
* for each `1 ≤ j ≤ k²`, a shortcut path `v₀ → a_j → v_k` of two shortcut arcs, each of cost `k`;
* demands `d_(v₀) = 2k`, `d_(vᵢ) = −1` for `1 ≤ i < k`, `d_(v_k) = −(k + 1)`, `d_(a_j) = 0`.

**Formalization Note** Vertex and arc types are `VertexS k` and `ArcS k` (0-based indices). The
demand of `path i` is `2k` if `i = 0`, else `−(k + 1)` if `i = k`, else `−1`; for `k ≥ 1` the
three cases are the paper's. -/
noncomputable def minCostFlowInstance (k : ℕ) : FlowInstance (VertexS k) (ArcS k) where
  tail
    | .fwd i => .path i.castSucc
    | .bwd i => .path i.succ
    | .scIn _ => .path 0
    | .scOut j => .shortcut j
  head
    | .fwd i => .path i.succ
    | .bwd i => .path i.castSucc
    | .scIn j => .shortcut j
    | .scOut _ => .path (Fin.last k)
  cost
    | .fwd _ => 1
    | .bwd _ => 1
    | .scIn _ => (k : ℝ)
    | .scOut _ => (k : ℝ)
  demand
    | .path i =>
        if i = 0 then 2 * (k : ℝ) else if i = Fin.last k then -((k : ℝ) + 1) else -1
    | .shortcut _ => 0

end Supplement

end IPMJumpLB


