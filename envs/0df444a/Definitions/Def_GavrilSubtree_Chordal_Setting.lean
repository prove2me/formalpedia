-- Prove2me | Definitions.Def_GavrilSubtree_Chordal_Setting
-- name    : GavrilSubtree_Chordal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:37:08.753618+00:00
-- url     : https://prove2.me/theorems/b8e1cb1d-e9c5-4328-a2a8-584e16a3f374
-- title:
--   §1–§3, pp. 47–54 — chordal graphs, subtree representations, (proper) subtree graphs, cliques μ(G), μ_v(G), clique trees, simplicial vertices
-- statement:
--   This file fixes the objects of Gavril's paper. Throughout, $G$ is a simple graph (undirected, no parallel edges, no loops) on a vertex set $V$.
--
--   1. **Chordal graph** (p. 48). $G$ is *chordal* if every simple circuit with more than three vertices has a *chord*: an edge of $G$ joining two vertices of the circuit that are not consecutive on it. Equivalently, for every cycle $C$ of length $L \ge 4$ there are vertices $x, y$ of $C$ with $xy \in E(G)$ and $xy$ not an edge of $C$.
--   2. **Subtree representation** (pp. 47–49). Let $T$ be a tree on a vertex set $\beta$. A family $F = (\bar v)_{v \in V}$ of subsets of $\beta$ *represents $G$ by subtrees of $T$* if every $\bar v$ is a *subtree* (a nonempty set of tree vertices inducing a connected subgraph of $T$) and, for all distinct $u, v \in V$,
--   $$u \sim_G v \iff \bar u \cap \bar v \neq \varnothing.$$
--   3. **Subtree graph** (p. 48). $G$ is a *subtree graph* if it has a subtree representation on some tree.
--   4. **Proper subtree graph** (p. 54). $G$ is a *proper subtree graph* if it has a subtree representation in which no subtree is contained in another: $\bar u \not\subseteq \bar v$ for all $u \neq v$.
--   5. **Cliques** (pp. 47, 50). A *completely connected set* is a set of pairwise adjacent vertices; a *clique* is a maximal completely connected set. $\mu(G)$ denotes the set of cliques of $G$, and $\mu_v(G) = \{A \in \mu(G) : v \in A\}$ the set of cliques containing $v$.
--   6. **Clique tree** (Theorem 2, p. 51). $G$ *has a clique tree* if there is a tree $T$ whose vertex set is $\mu(G)$ such that for every $v \in V$ the subgraph $T(\mu_v(G))$ induced on the cliques containing $v$ is connected (in particular nonempty).
--   7. **Simplicial vertex** (p. 48). Writing $\Gamma v$ for the set of neighbours of $v$, the vertex $v$ is *simplicial* if $\Gamma v$ is completely connected.
--
--   These are the notions in which the paper's main theorem, "a graph is a subtree graph if and only if it is chordal", is stated.
--
--   **Formalization Note** The paper's tree is a topological pattern whose subtrees are connected closed portions that may end inside an edge (pp. 48–49). Here a tree is a combinatorial tree `T : SimpleGraph β` with `T.IsTree`, and a subtree is a vertex set inducing a connected subgraph (Mathlib's `Connected` includes nonemptiness). Subdividing the topological tree at all end-points turns closed subtrees into vertex sets with the same intersection pattern, so the class of subtree graphs is the same. The tree is not required to be finite. The family is indexed by $V$, so two vertices may carry equal subtrees, and adjacency is compared only for distinct vertices since a simple graph has no loops. The tree's vertex type lives in the same universe as $V$, so that the clique tree on $\mu(G)$ is an admissible tree. Chordality is the cycle–chord definition, not a perfect-elimination ordering. "Clique" is `Maximal G.IsClique`; the paper's "completely connected set" is Mathlib's `G.IsClique`.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), pp. 47–54, §1 Introduction (pp. 47–49), §2 (p. 50, μ(G), μ_v(G)), Theorem 2 (p. 51), §3 (p. 54, proper subtree graph)

import Mathlib

namespace GavrilSubtree.Chordal

universe u

/-- §1, p. 48: a graph is chordal if every simple circuit with more than three vertices has an
edge connecting two non-consecutive vertices. A cycle walk of length `L` has `L` distinct
vertices and its edges are exactly the consecutive pairs, so a chord is an edge of `G` between
two vertices of the cycle that is not an edge of the cycle. -/
def IsChordal {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (c : G.Walk u u), c.IsCycle → 4 ≤ c.length →
    ∃ x ∈ c.support, ∃ y ∈ c.support, G.Adj x y ∧ s(x, y) ∉ c.edges

/-- §1, pp. 47–49: `F` represents `G` by subtrees of the tree `T`. Every `F v` is a subtree
(a nonempty vertex set inducing a connected subgraph of `T`), and two distinct vertices of `G`
are adjacent if and only if their subtrees intersect. -/
def IsSubtreeRep {V : Type u} {β : Type u} (G : SimpleGraph V) (T : SimpleGraph β)
    (F : V → Set β) : Prop :=
  T.IsTree ∧ (∀ v, (T.induce (F v)).Connected) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (F u ∩ F v).Nonempty)

/-- §1, p. 48: a subtree graph is the intersection graph of a family of subtrees of a tree. -/
def IsSubtreeGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (β : Type u) (T : SimpleGraph β) (F : V → Set β), IsSubtreeRep G T F

/-- §3, p. 54: a proper subtree graph is the intersection graph of a family of subtrees of a
tree so that no one of the subtrees is contained in another. -/
def IsProperSubtreeGraph {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (β : Type u) (T : SimpleGraph β) (F : V → Set β),
    IsSubtreeRep G T F ∧ ∀ u v, u ≠ v → ¬ F u ⊆ F v

/-- §1, p. 47 and §2, p. 50: `μ(G)`, the cliques of `G`, i.e. the maximal completely connected
sets of vertices. -/
def Cliques {V : Type u} (G : SimpleGraph V) : Type u :=
  {s : Set V // Maximal G.IsClique s}

/-- §2, p. 50: `μ_v(G)`, the set of cliques of `G` containing the vertex `v`. -/
def cliquesAt {V : Type u} (G : SimpleGraph V) (v : V) : Set (Cliques G) :=
  {A | v ∈ A.1}

/-- Theorem 2, p. 51: there is a tree `T` whose set of vertices is `μ(G)` such that, for every
vertex `v`, the subgraph `T(μ_v(G))` is connected. -/
def HasCliqueTree {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ T : SimpleGraph (Cliques G), T.IsTree ∧ ∀ v, (T.induce (cliquesAt G v)).Connected

/-- §1, p. 48: `v` is simplicial if `Γv`, the set of its neighbours, is completely connected. -/
def IsSimplicial {V : Type u} (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

end GavrilSubtree.Chordal


