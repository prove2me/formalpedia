-- Prove2me | Definitions.Def_NagamochiIbaraki_NodeConn_localNodeConn
-- name    : NagamochiIbaraki_NodeConn_localNodeConn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:07:31.85728+00:00
-- url     : https://prove2.me/theorems/754f94df-b8a8-41ef-9905-62421e95d7c5
-- title:
--   Local node-connectivity κ(x, y; (V, F)): |V| − 1 on adjacent pairs, otherwise the minimum node cut separating x and y
-- statement:
--   Let $G = (V, E)$ be a graph, $F \subseteq E$ a set of edges and $W \subseteq V$ a set of nodes. The graph $(V, F) - W$ is obtained from $(V, F)$ by deleting the nodes of $W$ together with their incident edges. For nodes $a, b$ we say that $b$ is reached from $a$ in $(V, F) - W$ if there is a sequence of nodes $a = v_0, v_1, \dots, v_m = b$, all outside $W$, in which consecutive nodes are joined by an edge of $F$ (the case $m = 0$, $a = b$, is allowed).
--
--   The **local node-connectivity** of two nodes $x, y$ in $(V, F)$ is
--
--   $$
--   \kappa(x, y; (V, F)) = \begin{cases} |V| - 1 & \text{if } x \text{ and } y \text{ are adjacent in } (V, F),\\[2pt] \min\{\, |W| : W \subseteq V - \{x, y\},\ x \text{ and } y \text{ are disconnected in } (V, F) - W \,\} & \text{otherwise.} \end{cases}
--   $$
--
--   This is the paper's convention: "$\kappa(x, y; G) = |V| - 1$ if $x$ and $y$ are adjacent". For non-adjacent distinct nodes the set $V - \{x, y\}$ always separates them, so the minimum is a natural number at most $|V| - 2$. The node connectivity of $G$ is $\kappa(G) = \min_{x, y} \kappa(x, y; G)$.
--
--   **Formalization Note** The value is taken in $\mathbb N_\infty$. For $x = y$ no node set avoiding $x$ separates $x$ from itself, so the infimum is over the empty set and equals $\top$; this makes statements "for any $x, y \in V$" hold trivially on the diagonal, as the paper intends. Reachability avoiding $W$ is the reflexive–transitive closure `ConnAvoid` of adjacency between nodes outside $W$.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 589, §3 first paragraph (definition of κ(x, y; G)); p. 593, proof of Theorem 3.1 (node cut sets W ⊆ V − {x, y})

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph

namespace NagamochiIbaraki.NodeConn

variable {V E : Type*}

/-- `ConnAvoid ends F W a b`: the node `b` is reached from the node `a` in the graph
`(V, F) − W`, i.e. by a sequence of nodes `a = v₀, v₁, …, v_m = b` in which consecutive nodes are
joined by an edge of `F` and every node lies outside `W`. (For `m = 0`, `a = b` and no condition
is imposed.) -/
def ConnAvoid (ends : E → Sym2 V) (F : Finset E) (W : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (fun u v => u ∉ W ∧ v ∉ W ∧ (edgeGraph ends F).Adj u v) a b

open Classical in
/-- The local node-connectivity `κ(x, y; (V, F))` of the nodes `x, y` in the spanning subgraph
`(V, F)` (p. 589): `|V| − 1` if `x` and `y` are adjacent in `(V, F)`; otherwise the minimum
size of a node set `W ⊆ V − {x, y}` such that `x` and `y` are disconnected in `(V, F) − W`.
The value lies in `ℕ∞`; it is `⊤` exactly when `x = y` (no node set avoiding `x` separates `x`
from itself). -/
noncomputable def localNodeConn [Fintype V] (ends : E → Sym2 V) (F : Finset E) (x y : V) : ℕ∞ :=
  if (edgeGraph ends F).Adj x y then ((Fintype.card V - 1 : ℕ) : ℕ∞)
  else ⨅ W ∈ {W : Finset V | x ∉ W ∧ y ∉ W ∧ ¬ ConnAvoid ends F W x y}, (W.card : ℕ∞)

end NagamochiIbaraki.NodeConn


