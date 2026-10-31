-- Prove2me | Definitions.Def_CombOpt_Circulation_IsPath
-- name    : CombOpt_Circulation_IsPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:21.375988+00:00
-- url     : https://prove2.me/theorems/ca6b2ccc-3684-4b1a-9ccb-a58837946683
-- title:
--   Paths in a digraph, with forward and reverse arcs
-- statement:
--   A **path** from $v_0$ to $v_k$ in a digraph is a sequence $v_0,e_1,v_1,\dots,e_k,v_k$ in which the ends of each arc $e_i$ are $v_{i-1}$ and $v_i$; nodes and arcs may repeat. The arc $e_i$ is **forward** if $t(e_i)=v_{i-1}$ and $h(e_i)=v_i$, and **reverse** otherwise.
--
--   **Formalization Note** The path is recorded from its first node as the list of pairs $(e_i,d_i)$, where the Boolean $d_i$ says whether $e_i$ is forward. A loop is always forward. The empty list is the one-node path.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19) and §2.2, p. 19 (PDF p. 28)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph

namespace CombOpt.Circulation

variable {V E : Type*}

/-- `IsPath G v p w`: the list `p` is a path of `G` from `v` to `w`, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19)
and §2.2, p. 19 (PDF p. 28). A path `v₀, e₁, v₁, …, e_k, v_k` (nodes and arcs may repeat) is
recorded from `v₀` as the list of pairs `(e_i, d_i)`, with `d_i = true` when `e_i` is a forward arc
(`t(e_i) = v_{i-1}`, `h(e_i) = v_i`) and `d_i = false` when `e_i` is a reverse arc (forward fails).

**Formalization Note** The flag records the direction of traversal and determines the next node.
A loop is always forward, as in the book ("forward if `t(e_i) = v_{i-1}` and `h(e_i) = v_i`, and
reverse otherwise"), hence the clause `G.tail e ≠ v` in the reverse case. The empty list is the
one-node path from `v` to `v`. -/
def IsPath (G : MultiDigraph V E) : V → List (E × Bool) → V → Prop
  | v, [], w => v = w
  | v, (e, true) :: p, w => G.tail e = v ∧ IsPath G (G.head e) p w
  | v, (e, false) :: p, w => G.head e = v ∧ G.tail e ≠ v ∧ IsPath G (G.tail e) p w

end CombOpt.Circulation


