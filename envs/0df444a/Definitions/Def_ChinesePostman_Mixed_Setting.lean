-- Prove2me | Definitions.Def_ChinesePostman_Mixed_Setting
-- name    : ChinesePostman_Mixed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:29.710648+00:00
-- url     : https://prove2.me/theorems/6f502a7a-3b7a-4ba9-ad1e-715c06deaac9
-- title:
--   §2, §6, §7, pp. 89, 115–119 — mixed multigraphs, degree, symmetric, even, connected, mixed tours, arborescences and the Rule
-- statement:
--   This file fixes the objects of §6 (*The mixed Euler tour problem*) of Edmonds and Johnson (1973), together with the graph and tour of §2 and the postman tour of §7.
--
--   1. **Mixed graph** (§2, p. 89; §6, p. 115). A mixed graph $G$ has a finite set $N$ of nodes and a finite set $E$ of edges; every edge meets two distinct nodes and several edges may meet the same pair of nodes. Some edges are **directed**: an edge directed away from node $i$ toward node $j$ must be traversed from $i$ to $j$ in any tour. The other edges are **undirected** and may be traversed in either direction.
--   2. **Degrees** (p. 115). The **degree** of a node is the total number of edges, regardless of direction, meeting it. $\operatorname{out}(n)$ and $\operatorname{in}(n)$ count the directed edges directed away from and toward $n$; $\deg_U(n)$ counts the undirected edges meeting $n$.
--   3. **Symmetric, even, connected** (p. 115). $G$ is **symmetric** when $\operatorname{out}(n) = \operatorname{in}(n)$ for every node $n$ (only directed edges count); **even** when every node has even degree (all edges count); **connected** when it is connected with the directions on the edges ignored. The directed edges form a **connected spanning subgraph** (p. 116) when every two nodes are joined by a walk, directions ignored, that uses only directed edges.
--   4. **Mixed tours** (§2, p. 89; §7, p. 119). A mixed walk is an alternating sequence $(n_1, e_1, n_2, \dots, e_l, n_{l+1})$ in which each directed $e_i$ is traversed from its tail $n_i$ to its head $n_{i+1}$ and each undirected $e_i$ meets $n_i$ and $n_{i+1}$. It is a **tour** when $n_{l+1} = n_1$; an **Euler tour** when it contains every edge exactly once; a **postman tour** when it contains every edge at least once. The one-node walk ($l = 0$) is allowed.
--   5. **Arborescence** (p. 115). An arborescence with root $r$ on a node set $W \ni r$ consists of directed edges $a_n$, $n \in W \setminus \{r\}$, with $a_n$ directed away from $n$ toward a node of $W$, such that following these edges from any node of $W$ leads to $r$; so every node $n \neq r$ of the tree has precisely one edge of it directed away from $n$. It is **maximal** when no directed edge is directed toward a node of $W$ and away from a node not in $W$, and **spanning** when $W = N$.
--   6. **The Rule** (p. 116). Given, at each node $n$, an ordering $U_n$ of the undirected edges meeting $n$ and an ordering $D_n$ of the directed edges away from $n$: whenever node $n$ is reached, leave $n$ by the next unused undirected edge if one is available; if all undirected edges at $n$ have been used, leave by the next unused edge directed away from $n$; if neither exists, stop. "Unused" refers to all edges used so far anywhere in the traversal.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** An edge carries two ends `tail`, `head` with `tail ≠ head` and a Boolean `directed`; for an undirected edge the order of the two ends has no meaning. Walks are a node list and an edge list of length one less, so parallel edges are distinguished. The arborescence uses a partial edge choice $a : N \to E \cup \{\mathrm{none}\}$: every non-root node of $W$ has a directed tree edge, and following its head reaches $r$ after finitely many steps. This includes the root-only tree when $E$ is empty. The Rule's traversal is computed with fuel (a step bound) and returns the node and edge sequences.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 89, §2 (graph, tour); p. 115, §6 (mixed graph, symmetric, degree, even, connected, arborescence, maximal arborescence); p. 116, §6 (directed edges forming a symmetric connected spanning subgraph, orderings, the Rule); p. 119, §7 (postman tour in a mixed graph)

import Mathlib

namespace ChinesePostman.Mixed

/-! Edmonds and Johnson (1973), §2, p. 89 (graphs, tours) and §6, pp. 115–118 (mixed graphs,
symmetric, even, connected, arborescences, the Rule of p. 116); §7, p. 119 (postman tours in a
mixed graph). -/

/-- A finite loopless mixed multigraph (§2, p. 89; §6, p. 115). Each edge `e` meets the two
distinct nodes `tail e` and `head e`; several edges may meet the same pair of nodes. When
`directed e = true`, the edge is directed away from `tail e` toward `head e` and must be traversed
from `tail e` to `head e`; when `directed e = false`, the edge is undirected and the order of
`tail e` and `head e` carries no meaning. -/
structure MixedGraph (V E : Type) where
  tail : E → V
  head : E → V
  directed : E → Bool
  loopless : ∀ e, tail e ≠ head e

variable {V E : Type}

/-- Edge `e` meets node `n`. -/
def MixedGraph.MeetsNode (G : MixedGraph V E) (e : E) (n : V) : Prop :=
  G.tail e = n ∨ G.head e = n

/-- The degree of a node (p. 115): the total number of edges, regardless of direction, meeting
the node. -/
def MixedGraph.degree [Fintype E] [DecidableEq V] (G : MixedGraph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => G.tail e = n ∨ G.head e = n)).card

/-- The number of directed edges directed away from `n`. -/
def MixedGraph.outDeg [Fintype E] [DecidableEq V] (G : MixedGraph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => G.directed e = true ∧ G.tail e = n)).card

/-- The number of directed edges directed toward `n`. -/
def MixedGraph.inDeg [Fintype E] [DecidableEq V] (G : MixedGraph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => G.directed e = true ∧ G.head e = n)).card

/-- The number of undirected edges meeting `n`. -/
def MixedGraph.undirDeg [Fintype E] [DecidableEq V] (G : MixedGraph V E) (n : V) : ℕ :=
  (Finset.univ.filter (fun e => G.directed e = false ∧ (G.tail e = n ∨ G.head e = n))).card

/-- A symmetric mixed graph (p. 115): every node has the same number of edges directed away
from it as directed toward it. -/
def MixedGraph.IsSymmetric [Fintype E] [DecidableEq V] (G : MixedGraph V E) : Prop :=
  ∀ n, G.outDeg n = G.inDeg n

/-- An even mixed graph (p. 115): every node has even degree (all edges counted). -/
def MixedGraph.IsEven [Fintype E] [DecidableEq V] (G : MixedGraph V E) : Prop :=
  ∀ n, Even (G.degree n)

/-- A walk that ignores directions and uses only edges satisfying `P`: an alternating sequence
`(n₁, e₁, …, e_l, n_{l+1})` in which `e_i` has ends `n_i` and `n_{i+1}` (in either order). The
one-node walk (`l = 0`) is allowed. -/
def MixedGraph.IsUndirWalkIn (G : MixedGraph V E) (P : E → Prop) (ns : List V) (es : List E) :
    Prop :=
  ∃ hlen : ns.length = es.length + 1,
    ∀ (i : ℕ) (h : i < es.length),
      P es[i] ∧
      ((G.tail es[i] = ns[i]'(by omega) ∧ G.head es[i] = ns[i + 1]'(by omega)) ∨
       (G.tail es[i] = ns[i + 1]'(by omega) ∧ G.head es[i] = ns[i]'(by omega)))

/-- A mixed graph is connected (p. 115) if it is connected when the directions on the edges are
ignored: every two nodes are joined by a walk ignoring directions. -/
def MixedGraph.Connected (G : MixedGraph V E) : Prop :=
  ∀ i j : V, ∃ ns es, G.IsUndirWalkIn (fun _ => True) ns es ∧
    ns.head? = some i ∧ ns.getLast? = some j

/-- The directed edges form a connected spanning subgraph (p. 116): every two nodes are joined by
a walk, ignoring directions, that uses directed edges only. -/
def MixedGraph.DirectedConnected (G : MixedGraph V E) : Prop :=
  ∀ i j : V, ∃ ns es, G.IsUndirWalkIn (fun e => G.directed e = true) ns es ∧
    ns.head? = some i ∧ ns.getLast? = some j

/-- A mixed walk: an alternating sequence `(n₁, e₁, …, e_l, n_{l+1})` in which a directed `e_i`
is traversed from its tail `n_i` to its head `n_{i+1}`, and an undirected `e_i` has ends `n_i`,
`n_{i+1}` in either order. The one-node walk (`l = 0`) is allowed. -/
def MixedGraph.IsMixedWalk (G : MixedGraph V E) (ns : List V) (es : List E) : Prop :=
  ∃ hlen : ns.length = es.length + 1,
    ∀ (i : ℕ) (h : i < es.length),
      (G.tail es[i] = ns[i]'(by omega) ∧ G.head es[i] = ns[i + 1]'(by omega)) ∨
      (G.directed es[i] = false ∧
        G.tail es[i] = ns[i + 1]'(by omega) ∧ G.head es[i] = ns[i]'(by omega))

/-- A tour of a mixed graph: a closed mixed walk (`n_{l+1} = n₁`). -/
def MixedGraph.IsMixedTour (G : MixedGraph V E) (ns : List V) (es : List E) : Prop :=
  G.IsMixedWalk ns es ∧ ns.head? = ns.getLast?

/-- A (mixed) Euler tour: a tour of the mixed graph containing every edge exactly once, every
directed edge traversed in its direction. -/
def MixedGraph.IsMixedEulerTour [DecidableEq E] (G : MixedGraph V E) (ns : List V)
    (es : List E) : Prop :=
  G.IsMixedTour ns es ∧ ∀ e : E, es.count e = 1

/-- A postman tour in a mixed graph (§7, p. 119): a tour using every edge at least once, every
directed edge traversed in its direction. -/
def MixedGraph.IsMixedPostmanTour (G : MixedGraph V E) (ns : List V) (es : List E) : Prop :=
  G.IsMixedTour ns es ∧ ∀ e : E, e ∈ es

/-- The parent map of an arborescence given by its optional edges `a n`: from a non-root
node with an assigned edge, follow that edge to its head; the root is fixed. The value for
nodes without an assigned edge is immaterial to an arborescence on `W`. -/
def MixedGraph.parent [DecidableEq V] (G : MixedGraph V E) (r : V) (a : V → Option E)
    (n : V) : V :=
  if n = r then r else (a n).elim n G.head

/-- An arborescence with root `r` on the node set `W`, made of directed edges (p. 115): every
node `n ∈ W`, except `n = r`, has precisely one edge `a n` of the arborescence directed away from
it, toward a node of `W`, and following these edges from any node of `W` leads to `r` (so the
edges `a n` form a tree on `W`). -/
def MixedGraph.IsArborescence [DecidableEq V] (G : MixedGraph V E) (W : Finset V) (r : V)
    (a : V → Option E) : Prop :=
  r ∈ W ∧
  (∀ n ∈ W, n ≠ r → ∃ e, a n = some e ∧ G.directed e = true ∧
    G.tail e = n ∧ G.head e ∈ W) ∧
  (∀ n ∈ W, ∃ k : ℕ, (G.parent r a)^[k] n = r)

/-- An arborescence on `W` is maximal (p. 115) when no directed edge is directed toward a node
of `W` and away from a node not in `W`. -/
def MixedGraph.IsMaximalNodeSet (G : MixedGraph V E) (W : Finset V) : Prop :=
  ∀ e, G.directed e = true → G.head e ∈ W → G.tail e ∈ W

/-- The other end of edge `e` as seen from node `n`. -/
def MixedGraph.otherEnd [DecidableEq V] (G : MixedGraph V E) (e : E) (n : V) : V :=
  if G.tail e = n then G.head e else G.tail e

/-- The edge the Rule (p. 116) chooses at node `n` once the edges in `used` have been used: the
first unused edge of the ordering `U n` of the undirected edges meeting `n`; if all of them are
used, the first unused edge of the ordering `D n` of the directed edges away from `n`; if none,
`none`. -/
def ruleNext [DecidableEq E] (U D : V → List E) (used : List E) (n : V) : Option E :=
  match (U n).find? (fun e => decide (e ∉ used)) with
  | some e => some e
  | none => (D n).find? (fun e => decide (e ∉ used))

/-- The traversal by the Rule (p. 116) from node `n` with the edges in `used` already used, run
for at most `fuel` steps: the node sequence and the edge sequence. It stops when the Rule finds no
unused edge at the current node. -/
def ruleRun [DecidableEq V] [DecidableEq E] (G : MixedGraph V E) (U D : V → List E) :
    ℕ → V → List E → List V × List E
  | 0, n, _ => ([n], [])
  | k + 1, n, used =>
    match ruleNext U D used n with
    | none => ([n], [])
    | some e =>
      let p := ruleRun G U D k (G.otherEnd e n) (used ++ [e])
      (n :: p.1, e :: p.2)

end ChinesePostman.Mixed


