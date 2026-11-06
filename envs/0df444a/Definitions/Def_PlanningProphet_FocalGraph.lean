-- Prove2me | Definitions.Def_PlanningProphet_FocalGraph
-- name    : PlanningProphet_FocalGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:45.18292+00:00
-- url     : https://prove2.me/theorems/9ac18af0-0136-4376-b0ee-a033e60b8e43
-- title:
--   §4.1 — the width-1 graphs $G_i$ with artificial edges
-- statement:
--   This module builds the graphs $G_1,\dots,G_k$ of the proof of Theorem 4 (§4.1, p.12; Figure 5, p.13).
--
--   Fix an $s,t$-path $P_i$. The graph $G_i$ has node set $V(P_i)$ and one edge for every edge $e$ of $G$ that starts at a node $u\in V(P_i)$ (the set $E^+(P_i)$):
--
--   1. if $e=(u,v)$ ends in $v\in V(P_i)$, it is kept as is;
--   2. if $v\notin V(P_i)$, it becomes the **artificial** edge $e'=(u,v')$, where $v'$ is the earliest node of $V(P_i)$, in the order in which $P_i$ visits them, that can be reached from $v$.
--
--   Labels and capacities are copied, the start and target are $s$ and $t$, and the value of an edge of $G_i$ is the value of the edge of $G$ it comes from: $w_{e'}=w_e$. Edges of $G$ that start outside $V(P_i)$ do not appear in $G_i$.
--
--   The graph $G_i$ is the width-1 instance on which the proof of Theorem 4 runs the algorithm of Theorem 3.
--
--   **Formalization Note** The node type is $\{t\}\cup V(P_i)$, which equals $V(P_i)$ when $P_i$ is an $s,t$-path. If no node of $V(P_i)$ is reachable from $v$, the head is set to $t$; this does not happen when every node reaches $t$, as in a graph covered by $s,t$-paths.
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, p.12 (construction of G_i, artificial edges); Figure 5, p.13

import Mathlib
import Definitions.Def_PlanningProphet_Model

namespace PlanningProphet

/-! # The graphs `Gᵢ` of the proof of Theorem 4 (arXiv:2406.13911v1, §4.1, p.12, and Figure 5)

"In graph `Gᵢ`, we take the graph that has `V(Pᵢ)` as the set of nodes and has all edges between
nodes in `V(Pᵢ)`. Then, for every edge `e` that starts at a node `u ∈ V(Pᵢ)` and ends in a node
`v ∉ V(Pᵢ)`, let `v′` be the earliest node in `V(Pᵢ)` (in the ordering induced by `Pᵢ`) such that
there is a path from `v` to `v′`. […] We add an edge `e′ = (u, v′)` with value `w_{e′} := w_e`.
We call these edges artificial."

**Formalization Note.**
1. The edges of `Gᵢ` are the edges `e` of `G` with `tail e ∈ V(Pᵢ)` (the paper's `E⁺(Pᵢ)`): an
   edge with both endpoints in `V(Pᵢ)` keeps its head, and the artificial edge `e′` is represented
   by `e` itself with head `v′`. Edges that start outside `V(Pᵢ)` are dropped. Labels and
   capacities are copied (the artificial edge `e′` carries the labels of `e`), and the value of an
   edge of `Gᵢ` is the value of the edge of `G` it comes from, `w ∘ Subtype.val`.
2. The node set is `{t} ∪ V(Pᵢ)`, which is `V(Pᵢ)` whenever `Pᵢ` is an `s,t`-path (it ends at
   `t`); writing `t` explicitly makes `t` a node of `Gᵢ` by construction.
3. `v′` is the first node of the list `V(Pᵢ)` (the order in which `Pᵢ` visits them) reachable from
   `v`. If none is reachable the head is `t`; this never happens when every node reaches `t`
   ("there is always a path from `v` to `t`, and `t ∈ V(Pᵢ)`, so there is always a node `v′`").
   The start node of `Gᵢ` is `s`. -/

variable {V E L : Type}

namespace Graph

variable (G : Graph V E L) [DecidableEq V]

open Classical in
/-- The head of an edge of `Gᵢ` (arXiv:2406.13911v1, §4.1, p.12): `head e` if it lies in `V(P)`,
and otherwise the earliest node `v′` of `V(P)`, in the order of `P`, reachable from `head e`. -/
noncomputable def focalHead (P : List E) (e : {e : E // G.tail e ∈ G.vertices P}) :
    {v : V // v ∈ G.t :: G.vertices P} :=
  if h : G.head e.1 ∈ G.vertices P then ⟨G.head e.1, List.mem_cons_of_mem _ h⟩
  else
    match hf : (G.vertices P).find? (fun v => decide (G.Reach (G.head e.1) v)) with
    | some v => ⟨v, List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hf)⟩
    | none => ⟨G.t, List.mem_cons_self⟩

/-- The graph `Gᵢ` built from the `s,t`-path `P = Pᵢ` (arXiv:2406.13911v1, §4.1, p.12; Figure 5):
nodes `V(P)`, edges the edges of `G` that start in `V(P)`, each with its head kept or redirected
to `v′` (`focalHead`), the same labels and capacities, start `s` and target `t`. -/
noncomputable def focal (P : List E) :
    Graph {v : V // v ∈ G.t :: G.vertices P} {e : E // G.tail e ∈ G.vertices P} L where
  tail e := ⟨G.tail e.1, List.mem_cons_of_mem _ e.2⟩
  head e := G.focalHead P e
  s := ⟨G.s, List.mem_cons_of_mem _ List.mem_cons_self⟩
  t := ⟨G.t, List.mem_cons_self⟩
  labels e := G.labels e.1
  cap := G.cap

end Graph

end PlanningProphet


