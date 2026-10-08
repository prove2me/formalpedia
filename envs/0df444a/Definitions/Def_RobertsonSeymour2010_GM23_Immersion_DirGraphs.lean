-- Prove2me | Definitions.Def_RobertsonSeymour2010_GM23_Immersion_DirGraphs
-- name    : RobertsonSeymour2010_GM23_Immersion_DirGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:48.25344+00:00
-- url     : https://prove2.me/theorems/d43af197-5c58-4a89-849e-b94089a8c29a
-- title:
--   Directed graphs with loops and parallel edges, their subgraphs, and connectivity (for 1.7, p. 4)
-- statement:
--   This module fixes the directed graphs that appear in result 1.7 of *Graph Minors XXIII*.
--
--   1. **Directed graph.** A directed graph $G$ has a finite vertex set $V(G)$, a finite edge set $E(G)$, and for every edge $e$ a **head** and a **tail** in $V(G)$. The edge $e$ is a **loop** if its head equals its tail. Loops and parallel edges are allowed.
--
--   2. **Subgraph.** A subgraph of $G$ is a pair $(W,F)$ with $W\subseteq V(G)$, $F\subseteq E(G)$, and the head and tail of every edge of $F$ in $W$. Its vertex set is $V(W,F)=W$.
--
--   3. **Connected subgraph.** A subgraph $(W,F)$ is connected if $W\ne\emptyset$ and any two vertices of $W$ are joined by a walk in the underlying undirected graph of $(W,F)$, i.e. a sequence of edges of $F$, each traversed in either direction.
--
--   **Formalization Note.** The structure is `DirGraph V E` with `head tail : E → V` (named to avoid Mathlib's simple `Digraph`). Connectivity is the reflexive–transitive closure of "joined by an edge of $F$ in either direction", restricted to the subgraph's vertices, plus non-emptiness. Finiteness is imposed by `Fintype` hypotheses in the theorem.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.7, p. 4 (directed graphs and connected subgraphs, used without definition in the paper)

import Mathlib

namespace RobertsonSeymour2010.GM23.Immersion

/-- A directed graph (p. 4): vertices `V`, edges `E`, and for each edge a head and a tail.
Loops (`head e = tail e`) and parallel edges are allowed. Finiteness is imposed by `Fintype`
binders in the theorems. -/
structure DirGraph (V E : Type) where
  /-- The head of each edge. -/
  head : E → V
  /-- The tail of each edge. -/
  tail : E → V

namespace DirGraph

variable {V E : Type}

/-- An edge is a loop if its head and tail coincide. -/
def IsLoop (G : DirGraph V E) (e : E) : Prop := G.head e = G.tail e

/-- A subgraph of a directed graph: a vertex set and an edge set, each chosen edge having its head
and tail in the chosen vertex set. -/
structure Subgraph (G : DirGraph V E) where
  /-- Vertex set. -/
  verts : Set V
  /-- Edge set. -/
  edges : Set E
  head_mem : ∀ e ∈ edges, G.head e ∈ verts
  tail_mem : ∀ e ∈ edges, G.tail e ∈ verts

/-- A subgraph is connected if it has at least one vertex and any two of its vertices are joined by
a walk using its edges, each edge traversed in either direction. -/
def Subgraph.Connected {G : DirGraph V E} (S : G.Subgraph) : Prop :=
  S.verts.Nonempty ∧
    ∀ x ∈ S.verts, ∀ y ∈ S.verts,
      Relation.ReflTransGen
        (fun a b => ∃ e ∈ S.edges,
          (G.head e = a ∧ G.tail e = b) ∨ (G.head e = b ∧ G.tail e = a)) x y

end DirGraph

end RobertsonSeymour2010.GM23.Immersion


