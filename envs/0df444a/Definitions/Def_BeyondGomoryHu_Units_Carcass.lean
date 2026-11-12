-- Prove2me | Definitions.Def_BeyondGomoryHu_Units_Carcass
-- name    : BeyondGomoryHu_Units_Carcass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:49.381393+00:00
-- url     : https://prove2.me/theorems/0ea54c74-7261-48b1-a73e-8bc817a4f664
-- title:
--   Cactus, canonical cuts, proper paths and the carcass properties of Theorems 2.2–2.3
-- statement:
--   **Definition 2.1.** A **cactus** $H$ is a connected graph in which no two cycles share a node. Edges and nodes on cycles are cycle-edges/-nodes, the others tree-edges/-nodes. A **canonical cut** $C$ is one tree-edge or two non-adjacent cycle-edges of the same cycle; the **sides** of $C$ are the components of $H-C$. A **proper path** is a simple path with at most one edge from each cycle; it is determined by its endpoints.
--
--   **Carcass data** for a terminal set $S$ consist of a graph $H_S$ on a finite node set, the set of terminals contained in each node (empty nodes contain none), and for each vertex $v$ a projection $\pi_S(v)$ given by the two endpoints of a proper path. An $S$-mincut is **represented** by $C$ if it induces the partition of $S$ into the terminals of the two sides of $C$; $v$ is **distinguished** by $C$ if it is distinguished by that partition.
--
--   The **skeleton properties** (Theorem 2.2): $H_S$ is a cactus; its nonempty nodes are tree-nodes and contain exactly the sets $S\cap U$ for the terminal $S$-units $U$, each once; every empty node has degree $\ge3$, exactly $3$ if it is a cycle-node; canonical cuts correspond bijectively to valid partitions. The **projection properties** (Theorem 2.3): each $\pi_S(v)$ is a proper path; for stretched $v$ it has distinct endpoints, starts and ends by tree-edges, and $C$ distinguishes $v$ iff the endpoints lie on different sides of $C$ (iff $C$ contains an edge of $\pi_S(v)$); for non-stretched $v$ it is a tree-node, the terminal node of $v$ when $v\in S$; and if $C$ keeps $\pi_S(v)$ entirely on the side of $S_1$, every $S$-mincut inducing $S_1,S_2$ keeps $v$ with $S_1$. A **carcass** satisfies both.
--
--   **Formalization Note.** Graphs are Mathlib simple graphs, so every cycle has at least three nodes. The count $O(d(S))$ of empty nodes is not part of the predicate; it is stated in Theorem 2.2.
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Definition 2.1, Theorems 2.2–2.3, pp. 3–4 (PDF 5–6)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Cuts

set_option autoImplicit false

namespace BeyondGomoryHu.Units

/-!
Section 2 (pp. 3–4): Definition 2.1 (cactus, canonical cuts, sides, proper paths) and the data and
properties of the connectivity carcass listed in Theorem 2.2 (skeleton) and Theorem 2.3
(projections).
-/

open Classical

section Cactus

variable {N : Type} [Fintype N] (H : SimpleGraph N)

/-- `e` is a cycle-edge: it lies on some cycle of `H`. -/
def IsCycleEdge (e : Sym2 N) : Prop :=
  ∃ (u : N) (p : H.Walk u u), p.IsCycle ∧ e ∈ p.edges

/-- `e` is a tree-edge: an edge of `H` lying on no cycle. -/
def IsTreeEdge (e : Sym2 N) : Prop :=
  e ∈ H.edgeSet ∧ ¬ IsCycleEdge H e

/-- `c` is a cycle-node: it lies on some cycle of `H`. -/
def IsCycleNode (c : N) : Prop :=
  ∃ p : H.Walk c c, p.IsCycle

/-- `c` is a tree-node: it lies on no cycle. -/
def IsTreeNode (c : N) : Prop :=
  ¬ IsCycleNode H c

/-- The edges `e₁, e₂` lie on a common cycle. -/
def OnCommonCycleEdges (e₁ e₂ : Sym2 N) : Prop :=
  ∃ (u : N) (p : H.Walk u u), p.IsCycle ∧ e₁ ∈ p.edges ∧ e₂ ∈ p.edges

/-- The nodes `c, d` lie on a common cycle. -/
def OnCommonCycle (c d : N) : Prop :=
  ∃ (u : N) (p : H.Walk u u), p.IsCycle ∧ c ∈ p.support ∧ d ∈ p.support

/-- Definition 2.1: a cactus is a connected graph in which no two cycles share a node (two cycles
through the same node have the same edges). -/
def IsCactus : Prop :=
  H.Connected ∧ ∀ (c : N) (p q : H.Walk c c), p.IsCycle → q.IsCycle →
    p.edges.toFinset = q.edges.toFinset

/-- Definition 2.1: a canonical cut is one tree-edge, or two non-adjacent cycle-edges of the same
cycle. -/
def IsCanonicalCut (C : Set (Sym2 N)) : Prop :=
  (∃ e, IsTreeEdge H e ∧ C = {e}) ∨
  (∃ e₁ e₂, e₁ ∈ H.edgeSet ∧ e₂ ∈ H.edgeSet ∧ e₁ ≠ e₂ ∧ OnCommonCycleEdges H e₁ e₂ ∧
    (∀ c, c ∈ e₁ → c ∉ e₂) ∧ C = {e₁, e₂})

/-- The nodes `c, d` are on the same side of `C`: connected in `H` with the edges of `C`
removed. -/
def SameSide (C : Set (Sym2 N)) (c d : N) : Prop :=
  (H.deleteEdges C).Reachable c d

/-- Definition 2.1: a proper path is a simple path with at most one edge from each cycle. -/
def IsProperWalk {a b : N} (p : H.Walk a b) : Prop :=
  p.IsPath ∧ ∀ e₁ ∈ p.edges, ∀ e₂ ∈ p.edges, IsCycleEdge H e₁ → OnCommonCycleEdges H e₁ e₂ →
    e₁ = e₂

/-- There is a proper path from `a` to `b`. -/
def HasProperPath (a b : N) : Prop :=
  ∃ p : H.Walk a b, IsProperWalk H p

/-- The nodes of the proper path between `a` and `b` (it is unique when it exists). -/
def ppNodes (a b : N) : Set N :=
  {c | ∃ p : H.Walk a b, IsProperWalk H p ∧ c ∈ p.support}

/-- The edges of the proper path between `a` and `b`. -/
def ppEdges (a b : N) : Set (Sym2 N) :=
  {e | ∃ p : H.Walk a b, IsProperWalk H p ∧ e ∈ p.edges}

/-- The proper path(s) from `a` to `b` start and end by tree-edges. -/
def EndsByTreeEdges (a b : N) : Prop :=
  ∀ p : H.Walk a b, IsProperWalk H p →
    (∀ e ∈ p.edges.head?, IsTreeEdge H e) ∧ (∀ e ∈ p.edges.getLast?, IsTreeEdge H e)

end Cactus

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Carcass data for a terminal set: a graph `H` on the nodes `N` (the skeleton), the set of
terminals `terms c` contained in each node `c` (empty for an empty node), and the projection of
each vertex, given by the two endpoints of a proper path (equal endpoints: a single node). -/
structure Carcass (V N : Type) where
  H : SimpleGraph N
  terms : N → Finset V
  proj : V → N × N

variable {N : Type} [Fintype N]

/-- The terminals lying on the side of `C` containing the node `c`. -/
def sideTerms (K : Carcass V N) (C : Set (Sym2 N)) (c : N) : Set V :=
  {s | ∃ d, SameSide K.H C c d ∧ s ∈ K.terms d}

/-- The terminals contained in a set of nodes (an `α`-component or `αβ`-component is identified
with this set). -/
def compTerms (K : Carcass V N) (T : Set N) : Set V :=
  {s | ∃ d ∈ T, s ∈ K.terms d}

/-- The nodes of the projection `π(v)`. -/
def projNodes (K : Carcass V N) (v : V) : Set N :=
  ppNodes K.H (K.proj v).1 (K.proj v).2

/-- The edges of the projection `π(v)`. -/
def projEdges (K : Carcass V N) (v : V) : Set (Sym2 N) :=
  ppEdges K.H (K.proj v).1 (K.proj v).2

/-- The `S`-mincut `A` is represented by the canonical cut `C`: `A` induces the partition of `S`
into the terminals of the two sides of `C`. -/
def Represents (G : WGraph V) (S : Finset V) (K : Carcass V N) (C : Set (Sym2 N))
    (A : Finset V) : Prop :=
  IsMincut G S A ∧ ∃ c, sideTerms K C c = ((A ∩ S : Finset V) : Set V)

/-- The vertex `v` is distinguished by the canonical cut `C`: it is distinguished by the valid
partition corresponding to `C`. -/
def DistinguishedByCut (G : WGraph V) (S : Finset V) (K : Carcass V N) (C : Set (Sym2 N))
    (v : V) : Prop :=
  ∃ c, DistinguishedBy G S (sideTerms K C c) v

/-- The properties of the skeleton `H_S` listed in Theorem 2.2 (without the `O(d(S))` count of
empty nodes, which is stated in Theorem 2.2 itself). -/
def IsSkeleton (G : WGraph V) (S : Finset V) (K : Carcass V N) : Prop :=
  IsCactus K.H ∧
  (∀ c, K.terms c ⊆ S) ∧
  (∀ c, (K.terms c).Nonempty → IsTreeNode K.H c) ∧
  (∀ c, (K.terms c).Nonempty → ∃ s ∈ S, K.terms c = S.filter (fun t => SEquiv G S s t)) ∧
  (∀ s ∈ S, ∃ c, K.terms c = S.filter (fun t => SEquiv G S s t)) ∧
  (∀ c d, (K.terms c).Nonempty → K.terms c = K.terms d → c = d) ∧
  (∀ c, K.terms c = ∅ → 3 ≤ K.H.degree c ∧ (IsCycleNode K.H c → K.H.degree c = 3)) ∧
  (∀ C, IsCanonicalCut K.H C → ∃ A, Represents G S K C A) ∧
  (∀ A, IsMincut G S A → ∃ C, IsCanonicalCut K.H C ∧ Represents G S K C A) ∧
  (∀ C C' A, IsCanonicalCut K.H C → IsCanonicalCut K.H C' →
    Represents G S K C A → Represents G S K C' A → C = C')

/-- The properties of the projections listed in Theorem 2.3. -/
def IsProjection (G : WGraph V) (S : Finset V) (K : Carcass V N) : Prop :=
  (∀ v, HasProperPath K.H (K.proj v).1 (K.proj v).2) ∧
  (∀ v, Stretched G S v →
    (K.proj v).1 ≠ (K.proj v).2 ∧ EndsByTreeEdges K.H (K.proj v).1 (K.proj v).2 ∧
    ∀ C, IsCanonicalCut K.H C →
      (DistinguishedByCut G S K C v ↔ ¬ SameSide K.H C (K.proj v).1 (K.proj v).2) ∧
      (¬ SameSide K.H C (K.proj v).1 (K.proj v).2 ↔ ∃ e ∈ C, e ∈ projEdges K v)) ∧
  (∀ v, ¬ Stretched G S v → (K.proj v).1 = (K.proj v).2 ∧ IsTreeNode K.H (K.proj v).1) ∧
  (∀ v ∈ S, (K.proj v).1 = (K.proj v).2 ∧ v ∈ K.terms (K.proj v).1) ∧
  (∀ v C c, IsCanonicalCut K.H C → (∀ d ∈ projNodes K v, SameSide K.H C c d) →
    ∀ A, IsMincut G S A → InducesSide S A (sideTerms K C c) → OnSide S A (sideTerms K C c) v)

/-- A connectivity carcass of `S`: a skeleton with projections (Theorems 2.2 and 2.3). -/
def IsCarcass (G : WGraph V) (S : Finset V) (K : Carcass V N) : Prop :=
  IsSkeleton G S K ∧ IsProjection G S K

end BeyondGomoryHu.Units


