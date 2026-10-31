-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_IsOneTree
-- name    : CombOpt_HeldKarp_Graph_IsOneTree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:43.06881+00:00
-- url     : https://prove2.me/theorems/d6ad3643-aac7-499d-adb6-65fcd03acf90
-- title:
--   1-tree
-- statement:
--   Let $v_1\in V$. A **1-tree** of $G$ (with respect to $v_1$) is an edge set $J=\{e,f\}\cup T$, where $e\ne f$ are two edges of $\delta(v_1)$ (possibly parallel) and $T$ is a spanning tree of $G\setminus v_1$.
--
--   Every tour is a 1-tree when $G$ has at least two nodes, which is what makes minimum 1-trees a lower bound for the TSP.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, p. 253 (PDF p. 261)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_cut
import Definitions.Def_CombOpt_HeldKarp_Graph_IsSpanningTreeDelete

namespace CombOpt.HeldKarp

/-- **A 1-tree.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, p. 253
(PDF p. 261): "a set of edges consisting of two edges incident with node v_1 plus a spanning tree of
G \ v_1 is called a 1-tree."

`G.IsOneTree v₁ J` says `J = {e, f} ∪ T` for two distinct edges `e, f ∈ δ(v₁)` and a spanning tree
`T` of `G \ v₁`.

**Formalization Note.** "Incident with v₁" is read as `e ∈ δ(v₁)`, as in the 1-tree Bound box on the
same page ("e, f ∈ δ(v_1), e ≠ f"); `e` and `f` may be parallel. -/
def Graph.IsOneTree {V E : Type*} [Fintype E] [DecidableEq E] (G : Graph V E)
    (v₁ : V) (J : Finset E) : Prop :=
  ∃ (e f : E) (T : Finset E), e ≠ f ∧ e ∈ G.cut {v₁} ∧ f ∈ G.cut {v₁} ∧
    G.IsSpanningTreeDelete v₁ T ∧ J = insert e (insert f T)

end CombOpt.HeldKarp


