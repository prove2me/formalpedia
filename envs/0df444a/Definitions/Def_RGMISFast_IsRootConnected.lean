-- Prove2me | Definitions.Def_RGMISFast_IsRootConnected
-- name    : RGMISFast_IsRootConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.020228+00:00
-- url     : https://prove2.me/theorems/6c688960-2c18-4907-b2f7-d2fd9c9b3495
-- title:
--   Root-connected and attached sets, outer boundary $N^-[A]$, and $d(W)$
-- statement:
--   Let $G$ (or $H$) be a finite simple graph with root $u^*$.
--
--   1. A vertex set $A$ is **root-connected** if $u^*\in A$ and the induced subgraph $G[A]$ is connected; equivalently every vertex of $A$ is joined to $u^*$ by a path inside $A$. A set is **connected** if it is nonempty and $G[A]$ is connected.
--   2. A set $W\subseteq V(H)\setminus A$ is **attached** to $A$ if every vertex of $W$ can be reached from $A$ by a path inside $A\cup W$.
--   3. The **outer boundary** of $A$ is $N^-[A]=N^+[A]\setminus A$, the vertices outside $A$ with a neighbour in $A$.
--   4. For $W\subseteq V(H)\setminus\{u^*\}$, $d(W)$ counts the vertices of $W$ together with all vertices adjacent to $W$ or to $u^*$, not counting $u^*$ itself.
--
--   These notions describe the connected vertex sets that a query tree can explore.
--
--   **Formalization Note** Connectivity inside a set $S$ is reachability in the graph that keeps only the edges of $G$ with both endpoints in $S$ (the induced subgraph, kept on the whole vertex type).
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §2, p.10 (PDF p.12) (root-connected, N⁻); §5.1, p.17 (PDF p.19) (attached sets, d(W))

import Mathlib

set_option autoImplicit false

namespace RGMISFast

/-- The graph `G` with only the edges whose two endpoints lie in `S` (the induced subgraph `G[S]`,
kept on the whole vertex type: the vertices outside `S` become isolated). Helper for the
connectivity notions of the mission. -/
def restrictTo {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

/-- `A` is a nonempty vertex set whose induced subgraph `G[A]` is connected: any two vertices of
`A` are joined by a path all of whose vertices lie in `A`. -/
def IsConnectedSet {V : Type*} (G : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, ∀ y ∈ A, (restrictTo G ↑A).Reachable x y

/-- Root-connected sets (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy
MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §2, p.10): "A
vertex set A ⊆ V(G) is called root-connected if it contains the root u∗ and the induced subgraph
G[A] is connected. Equivalently, every vertex of A can be joined to u∗ by a path all of whose
vertices belong to A."

**Formalization Note** The second (equivalent) form is used: `u ∈ A` and every `x ∈ A` is
reachable from `u` in `G[A]`. -/
def IsRootConnected {V : Type*} (G : SimpleGraph V) (u : V) (A : Finset V) : Prop :=
  u ∈ A ∧ ∀ x ∈ A, (restrictTo G ↑A).Reachable u x

/-- Attached sets (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is
Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §5.1, p.17): "Let A be
a vertex set of a graph H. A set W ⊆ V(H) \ A is attached to A if every connected component of
H[A ∪ W] meets A; in other words, every vertex of W can be reached from A by a path inside
A ∪ W."

**Formalization Note** `W` is disjoint from `A`, and every `w ∈ W` is reachable in `H[A ∪ W]`
from some vertex of `A`. -/
def IsAttached {V : Type*} [DecidableEq V] (H : SimpleGraph V) (A W : Finset V) : Prop :=
  Disjoint A W ∧ ∀ w ∈ W, ∃ x ∈ A, (restrictTo H ↑(A ∪ W)).Reachable x w

open Classical in
/-- The outer boundary `N⁻[A] = N⁺[A] \ A`, the vertices outside `A` that have a neighbour in `A`
(Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every
Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §2, p.10). -/
noncomputable def outerBdry {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V) :
    Finset V :=
  Finset.univ.filter (fun v => v ∉ A ∧ ∃ x ∈ A, G.Adj x v)

open Classical in
/-- `d(W)` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at
Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §5.1, p.17): "Let d(W) count the
vertices of W together with all vertices adjacent to W or to u∗; u∗ itself is not counted here."
In a graph `H` with root `u`, `d(W)` is the number of vertices `x ≠ u` with `x ∈ W` or `x`
adjacent to a vertex of `{u} ∪ W`. -/
noncomputable def dW {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V)
    (W : Finset V) : ℕ :=
  (Finset.univ.filter (fun x => x ≠ u ∧ (x ∈ W ∨ ∃ y ∈ insert u W, H.Adj y x))).card

end RGMISFast


