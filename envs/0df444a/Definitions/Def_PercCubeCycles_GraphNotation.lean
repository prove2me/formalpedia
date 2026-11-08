-- Prove2me | Definitions.Def_PercCubeCycles_GraphNotation
-- name    : PercCubeCycles_GraphNotation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:26.50519+00:00
-- url     : https://prove2.me/theorems/c0491c97-9616-405e-a45a-306ef8c1e503
-- title:
--   Graph notation of §2: $G[A]$, $N_G(A)$, $e_G(A,B)$, $e_G(A)$, connected and almost connected sets, bare paths, the giant component, the 2-core
-- statement:
--   For a finite graph $G=(V,E)$ and $A,B\subseteq V$, the paper uses the following notation (p.6).
--
--   1. $G[A]$ is the subgraph induced by $A$, and $e_G(A)=|E(G[A])|$.
--   2. $N_G(A)$ is the set of vertices in $V\setminus A$ with a neighbour in $A$.
--   3. $e_G(A,B)$ is the number of edges with one endpoint in $A$ and one in $B$, with edges inside $A\cap B$ counted twice. Equivalently, it is the number of ordered pairs $(a,b)\in A\times B$ with $a\sim b$.
--   4. $S$ is **connected** in $G$ if $G[S]$ is connected, and **almost connected** if it is connected or $G[S\cup\{v\}]$ is connected for some $v\notin S$.
--   5. A path is **bare** in $G$ if all its internal vertices have degree two in $G$.
--
--   A **largest component** is a connected component with the most vertices. The **2-core** of $G$ (p.3) is the maximal subgraph of minimum degree at least 2, whose vertex set is the union of all sets $U$ on which $G[U]$ has minimum degree at least 2.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** `restrict G A` is $G[A]$ kept on all of `V`, with vertices outside $A$ isolated. `coreGraph G L` is the 2-core of the component $L$ in that form. The empty set is not connected.
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), §2, p.6; p.3; p.2

import Mathlib

set_option autoImplicit false

namespace PercCubeCycles

/-!
# Graph notation of §2

Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…), §2, p.6: `e_G(A,B)`, `N_G(A)`, `G[A]`, `e_G(A)`, connected and almost connected sets,
bare paths; p.3: the 2-core and every cycle lying in it; p.2 and p.6: the giant component.

**Formalization Note.**
* Graphs are `SimpleGraph V` on a finite type. `G[A]` is the graph `restrict G A` on all of `V`
  whose edges are those of `G` with both endpoints in `A`; vertices outside `A` are isolated in it.
  So degrees, neighbourhoods and subgraphs of `G[A]` are read in `restrict G A`.
* The empty set is not connected (`SimpleGraph.Connected` includes nonemptiness).
* `twoCore G` is the union of all vertex sets of minimum induced degree at least 2, i.e. the vertex
  set of the maximal subgraph of minimum degree at least 2.
-/

variable {V : Type*}

/-- p.6: `G[A]`, kept on the vertex type `V`: the edges of `G` with both endpoints in `A`. -/
def restrict (G : SimpleGraph V) (A : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => G.Adj u v ∧ u ∈ A ∧ v ∈ A

open scoped Classical in
/-- p.6: `N_G(A)`, the set of vertices in `V ∖ A` with a neighbour in `A`. -/
noncomputable def nbhd [Fintype V] (G : SimpleGraph V) (A : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ A ∧ ∃ a ∈ A, G.Adj a v

open scoped Classical in
/-- p.6: `e_G(A, B)`, the number of edges with one endpoint in `A` and one in `B`, with edges
inside `A ∩ B` counted twice: the number of ordered pairs `(a, b) ∈ A × B` with `a ~ b`. -/
noncomputable def eBetween (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  (G.interedges A B).card

/-- p.6: `e_G(A) = |E(G[A])|`. -/
noncomputable def edgesIn (G : SimpleGraph V) (A : Finset V) : ℕ :=
  (restrict G A).edgeSet.ncard

/-- p.6: `S` is connected in `G`: the induced subgraph `G[S]` is connected. -/
def IsConnectedSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected

/-- p.6: `S` is almost connected in `G`: it is connected in `G`, or `G[S ∪ {v}]` is connected for
some `v ∈ V(G) ∖ S`. -/
def IsAlmostConnectedSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsConnectedSet G S ∨ ∃ v, v ∉ S ∧ (G.induce (insert v (S : Set V))).Connected

open scoped Classical in
/-- The degree of `v` in `G`. -/
noncomputable def deg [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun u => G.Adj v u).card

/-- p.6: a path `P ⊆ G` is bare in `G`: all of its internal vertices have degree two in `G`. -/
def IsBarePath [Fintype V] (G : SimpleGraph V) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ ∀ x ∈ p.support.tail.dropLast, deg G x = 2

/-- `S` is the vertex set of a connected component of `G`. -/
def IsComponentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ c : G.ConnectedComponent, (S : Set V) = c.supp

/-- p.2, p.6: `S` is the vertex set of a largest connected component of `G`. Statements about the
giant component hold for every such `S`, so a tie for the largest component is covered. -/
def IsLargestComponent (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsComponentSet G S ∧ ∀ S', IsComponentSet G S' → S'.card ≤ S.card

open scoped Classical in
/-- `G[U]` has minimum degree at least 2. -/
def HasMinDegTwoOn [Fintype V] (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ v ∈ U, 2 ≤ (U.filter fun u => G.Adj v u).card

open scoped Classical in
/-- p.3: the vertex set of the 2-core of `G`, the maximal subgraph of `G` of minimum degree at
least 2: the union of all vertex sets on which the induced minimum degree is at least 2. -/
noncomputable def twoCore [Fintype V] (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => ∃ U, HasMinDegTwoOn G U ∧ v ∈ U

/-- p.17, Theorem 6, p.10: `C₂`, the 2-core of the component `L` of `G`, as a graph on `V`. -/
noncomputable def coreGraph [Fintype V] (G : SimpleGraph V) (L : Finset V) : SimpleGraph V :=
  restrict G (twoCore (restrict G L))

/-- `G` contains a cycle of length at least `L`. -/
def HasCycleAtLeast (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ L ≤ c.length

end PercCubeCycles


