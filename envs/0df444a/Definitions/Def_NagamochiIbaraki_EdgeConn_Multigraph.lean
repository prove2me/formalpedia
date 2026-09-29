-- Prove2me | Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
-- name    : NagamochiIbaraki_EdgeConn_Multigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:00:23.789285+00:00
-- url     : https://prove2.me/theorems/b6db65d1-d4b9-409f-b8e0-7fa71f41119b
-- title:
--   Finite loopless multigraphs: edge subgraphs, forests, maximal spanning forests and degrees
-- statement:
--   Throughout Nagamochi and Ibaraki's paper a graph $G = (V, E)$ is undirected, has $|V| \ge 2$ nodes, may have multiple (parallel) edges, and has no self-loop. We encode such a graph by a finite node set $V$, a finite edge set $E$, and a map $\mathrm{ends} \colon E \to \mathrm{Sym}^2 V$ sending each edge $e$ to the unordered pair $\{u, v\}$ of its end nodes. Two different edges may have the same pair of end nodes (parallel edges); the graph is **simple** when $\mathrm{ends}$ is injective. Every subset $F \subseteq E$ determines the **spanning subgraph** $(V, F)$.
--
--   This file introduces four notions for spanning subgraphs.
--
--   1. **Edge graph.** $\mathrm{edgeGraph}(F)$ is the simple graph on $V$ in which $u \ne v$ are adjacent when some edge of $F$ joins them. Two nodes are joined by a path in $(V, F)$ exactly when they are reachable from each other in $\mathrm{edgeGraph}(F)$.
--   2. **Forest.** $(V, F)$ is a **forest** when it contains no cycle, expressed as: every edge $e \in F$ with end nodes $u, v$ is a bridge of $F$, that is, $u$ and $v$ are not connected in $(V, F \setminus \{e\})$. Because edges are elements of $E$ and not pairs of nodes, two parallel edges between $u$ and $v$ form a cycle and are never together in a forest.
--   3. **Maximal spanning forest.** For $F \subseteq H \subseteq E$, $(V, F)$ is a **maximal spanning forest in** $(V, H)$ when $F$ is a forest and $F \cup \{e\}$ is not a forest for any $e \in H \setminus F$.
--   4. **Degree.** $\deg_F(v)$ is the number of edges of $F$ incident to $v$, parallel edges counted separately.
--
--   These notions are shared by every statement of the mission: Lemma 2.1 and Lemma 2.5 are about maximal spanning forests, Lemma 2.3 about forests, Lemma 2.4 about paths in the classes, and Lemma 2.6 about degrees.
--
--   **Formalization Note** Self-loops are excluded by the hypothesis $\forall e,\ \neg\,\mathrm{ends}(e).\mathrm{IsDiag}$ carried by each theorem, not by the definitions. "Spanning" is automatic, as the node set of every subgraph is all of $V$.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 583, §1 (standing assumptions); p. 584, §2 (multiple graphs) and Lemma 2.1 (maximal spanning forest); p. 589, Lemma 2.6 (degree)

import Mathlib

namespace NagamochiIbaraki.EdgeConn

/-! Finite multigraphs (Nagamochi–Ibaraki 1992, p. 583 and §2, p. 584).

A graph `G = (V, E)` is encoded by a node type `V`, an edge type `E` and the map
`ends : E → Sym2 V` sending each edge to its unordered pair of end nodes. Parallel edges are
distinct elements of `E` with the same image; self-loops are excluded by the hypothesis
`∀ e, ¬ (ends e).IsDiag` carried by the theorems, and simplicity is `Function.Injective ends`.
An edge subset is a `Finset E`. -/

variable {V E : Type*}

/-- The simple graph on `V` recording which pairs of nodes are joined by at least one edge of
`F`. Reachability in `edgeGraph ends F` is connectivity by a path using edges of `F` only;
multiplicities play no role in reachability. -/
def edgeGraph (ends : E → Sym2 V) (F : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (ends '' (F : Set E))

/-- `(V, F)` is a forest (a multigraph without cycles): every edge of `F` is a bridge of `F`,
i.e. removing it from `F` disconnects its two end nodes. Two parallel edges form a cycle, so
neither of them is a bridge. -/
def IsForest [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) : Prop :=
  ∀ e ∈ F, ∀ u v : V, ends e = s(u, v) → ¬ (edgeGraph ends (F.erase e)).Reachable u v

/-- `(V, F)` is a maximal spanning forest in the spanning subgraph `(V, H)`: `F ⊆ H`, `F` is a
forest, and adding any further edge of `H` to `F` creates a cycle. The node set is all of `V`,
so every such forest is spanning. -/
def IsMaxSpanningForest [DecidableEq E] (ends : E → Sym2 V) (H F : Finset E) : Prop :=
  F ⊆ H ∧ IsForest ends F ∧ ∀ e ∈ H, e ∉ F → ¬ IsForest ends (insert e F)

/-- The degree of the node `v` in the spanning subgraph `(V, F)`: the number of edges of `F`
incident to `v`, parallel edges counted separately. -/
def degIn [DecidableEq V] (ends : E → Sym2 V) (F : Finset E) (v : V) : ℕ :=
  (F.filter (fun e => v ∈ ends e)).card

end NagamochiIbaraki.EdgeConn


