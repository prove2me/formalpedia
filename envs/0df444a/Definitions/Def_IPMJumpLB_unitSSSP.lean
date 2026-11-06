-- Prove2me | Definitions.Def_IPMJumpLB_unitSSSP
-- name    : IPMJumpLB_unitSSSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:17.505206+00:00
-- url     : https://prove2.me/theorems/e325dcea-6e64-4456-80e1-37f27e1f394e
-- title:
--   The unit-demand single-source shortest path instance of Section 4
-- statement:
--   For parameters $b, k \in \mathbb N$ (the paper takes $b = \lceil 6/\alpha\rceil$ for $\alpha \in (0,1)$ and $k \ge 3$), the **unit-demand instance** is the min-cost flow instance on the vertices and arcs above with
--
--   1. path arcs $e_i^+ = (v_i, v_{i+1})$ and $e_i^- = (v_{i+1}, v_i)$, $0 \le i < k$, of cost $1$ (the bidirected **main path**; gadget $i$ is $\{e_i^+, e_i^-\}$);
--   2. $(b-2)k^2$ **shortcut paths** $v_0 \to a_j \to v_k$, each of two shortcut arcs of cost $k$;
--   3. $k-1$ leaves attached to each $v_i$, $1 \le i \le k$, and another $k^2$ leaves attached to $v_k$, each with a single incoming **leaf arc** from its parent, of cost $0$;
--   4. demands
--   $$
--   d_{v_0} = \hat n_k - 1 = bk^2, \qquad d_u = -1 \quad (u \ne v_0).
--   $$
--
--   It is a single-source shortest path instance in which one unit of flow is required at every vertex other than $v_0$. It is the hard instance of Theorem 4.1.
--
--   **Formalization Note** Vertex and arc types are `VertexU b k` and `ArcU b k`, with 0-based indices; `leaf i t` hangs on $v_{i+1}$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11 (main path from Section 3.1, p.6)

import Mathlib
import Definitions.Def_IPMJumpLB_FlowInstance
import Definitions.Def_IPMJumpLB_VertexU
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_nHat

namespace IPMJumpLB

/-- The unit-demand single-source shortest path instance of Section 4 (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11; the main
path from §3.1, p.6), with parameters `b, k ∈ ℕ` (the paper takes `b = ⌈6/α⌉` and `k ≥ 3`):

* the main path: for each `0 ≤ i < k`, a forward arc `e⁺ᵢ = (vᵢ, vᵢ₊₁)` and a backward arc
  `e⁻ᵢ = (vᵢ₊₁, vᵢ)`, each of cost `1`;
* `(b − 2)k²` shortcut paths `v₀ → a_j → v_k`, each of two shortcut arcs of cost `k`;
* `k − 1` leaves attached to each `vᵢ`, `1 ≤ i ≤ k`, and another `k²` leaves attached to `v_k`,
  each with a single incoming leaf arc from its parent, of cost `0`;
* demands `d_(v₀) = n̂_k − 1 = bk²` and `d_u = −1` for every vertex `u ≠ v₀`.

**Formalization Note** Vertex and arc types are `VertexU b k` and `ArcU b k` (0-based indices;
`leaf i t` hangs on `v_(i+1)`). -/
noncomputable def unitSSSP (b k : ℕ) : FlowInstance (VertexU b k) (ArcU b k) where
  tail
    | .fwd i => .path i.castSucc
    | .bwd i => .path i.succ
    | .scIn _ => .path 0
    | .scOut j => .shortcut j
    | .leafArc i _ => .path i.succ
    | .extraLeafArc _ => .path (Fin.last k)
  head
    | .fwd i => .path i.succ
    | .bwd i => .path i.castSucc
    | .scIn j => .shortcut j
    | .scOut _ => .path (Fin.last k)
    | .leafArc i t => .leaf i t
    | .extraLeafArc t => .extraLeaf t
  cost
    | .fwd _ => 1
    | .bwd _ => 1
    | .scIn _ => (k : ℝ)
    | .scOut _ => (k : ℝ)
    | .leafArc _ _ => 0
    | .extraLeafArc _ => 0
  demand
    | .path i => if i = 0 then (nHat b k : ℝ) - 1 else -1
    | .shortcut _ => -1
    | .leaf _ _ => -1
    | .extraLeaf _ => -1

end IPMJumpLB


