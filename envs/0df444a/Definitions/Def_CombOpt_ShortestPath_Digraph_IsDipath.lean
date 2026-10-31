-- Prove2me | Definitions.Def_CombOpt_ShortestPath_Digraph_IsDipath
-- name    : CombOpt_ShortestPath_Digraph_IsDipath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:00.893872+00:00
-- url     : https://prove2.me/theorems/a60592b2-e379-4538-9a77-6495b2a0699b
-- title:
--   Dipath from $u$ to $v$ (nodes and arcs may repeat)
-- statement:
--   A **path** in $G$ is a sequence $v_0,e_1,v_1,\dots,e_k,v_k$ ($k\ge0$) of nodes and arcs in which the arc $e_i$ joins $v_{i-1}$ and $v_i$. The arc $e_i$ is **forward** if $t(e_i)=v_{i-1}$ and $h(e_i)=v_i$, and a path all of whose arcs are forward is a **directed path** or **dipath** from $v_0$ to $v_k$.
--
--   Nodes and arcs may repeat in a dipath. The one-node sequence $v$ is a dipath from $v$ to $v$.
--
--   **Formalization Note** `G.IsDipath u P v` holds when the arc list $P=[e_1,\dots,e_k]$ is the arc sequence of a dipath from $u$ to $v$: either $P$ is empty and $u=v$, or $t(e_1)=u$ and $[e_2,\dots,e_k]$ is a dipath from $h(e_1)$ to $v$. The nodes of the dipath are $u,h(e_1),\dots,h(e_k)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 10 (PDF p. 19), paths; §2.2, p. 19 (PDF p. 28), forward arcs and dipaths

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph

namespace CombOpt.ShortestPath

/-- **A dipath (directed path, nodes and arcs may repeat).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 10 (PDF p. 19) and §2.2, p. 19 (PDF p. 28): a path is a sequence
v_0, e_1, v_1, …, e_k, v_k (k ≥ 0) whose i-th arc joins v_{i−1} and v_i; "An arc e_i of a path
P : v_0, e_1, v_1, …, e_k, v_k is *forward* if t(e_i) = v_{i−1} and h(e_i) = v_i … A path in which
every arc is forward is a *directed path* or *dipath*."

`G.IsDipath u P v` says that the list of arcs `P = [e_1, …, e_k]` is (the arc sequence of) a
dipath from `u` to `v`: either `P = []` and `u = v` (the one-node dipath, k = 0), or
`P = e :: P'` with `tail e = u` and `P'` a dipath from `head e` to `v`.

**Formalization Note.** A dipath is determined by its start node and its arc list; its nodes are
`u, head e_1, …, head e_k`. Nodes and arcs may repeat (a dipath need not be simple), exactly as
in the book. -/
inductive Digraph.IsDipath {V E : Type*} (G : Digraph V E) : V → List E → V → Prop
  /-- The dipath consisting of the single node `v` and no arcs. -/
  | nil (v : V) : G.IsDipath v [] v
  /-- Prepend the forward arc `e` with tail `u` to a dipath starting at `head e`. -/
  | cons {u v : V} (e : E) (P : List E) (h : G.tail e = u) (hP : G.IsDipath (G.head e) P v) :
      G.IsDipath u (e :: P) v

end CombOpt.ShortestPath


