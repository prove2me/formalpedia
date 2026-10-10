-- Prove2me | Definitions.Def_CircStability_Main_Closure
-- name    : CircStability_Main_Closure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:14.494472+00:00
-- url     : https://prove2.me/theorems/d2d0ed3c-d78e-4fc3-94fa-96f6cbafc86b
-- title:
--   p. 4, §2.1 p. 6 — k-closure, C-closure, locally maximal cycles, Hamiltonian-connected graphs
-- statement:
--   This module defines the closure operations and cycle notions used in §§2 and 4 of Ma and Ning.
--
--   1. **$k$-closed, $k$-closure** (p. 4). A graph $H$ is $k$-closed if every two distinct non-adjacent vertices $u,v$ satisfy $d_H(u)+d_H(v)<k$. The $k$-closure of $G$ is obtained by recursively joining non-adjacent pairs whose degree sum is at least $k$ until no such pair remains; equivalently it is the least $k$-closed graph containing $G$.
--   2. **$C$-closure** (p. 4). For a cycle $C$ of length $c$, the $C$-closure $\overline G$ is obtained from $G$ by replacing the induced subgraph $G[C]$ by its $(c+1)$-closure, with degrees computed in $G[C]$. In particular $G\subseteq\overline G$, and $\overline G$ and $G$ agree on every pair not contained in $V(C)$.
--   3. **Locally maximal cycle** (§2.1, p. 6). A cycle $C$ of $G$ is locally maximal if there is no cycle $C'$ of $G$ with $|E(C')|>|E(C)|$ and $|E(C')\cap E(C,G-C)|\le2$, where $E(C,G-C)$ is the set of edges between $V(C)$ and $V(G)\setminus V(C)$. Every longest cycle is locally maximal.
--   4. **Hamiltonian-connected** (§2.1, p. 6). $G$ is Hamiltonian-connected if any two distinct vertices $x,y$ are the ends of an $(x,y)$-path passing through every vertex of $G$.
--
--   The $C$-closure is the device by which the paper describes its extremal graphs exactly (Theorem 1.9); locally maximal cycles replace longest cycles in the proofs of §4.
--
--   **Formalization Note.** The $k$-closure is defined as the infimum of all $k$-closed supergraphs of $G$. This infimum is the recursive closure of the page: it contains $G$, it is itself $k$-closed, and it lies below every $k$-closed supergraph (all three facts are proved in a companion sanity file, not part of the mission). The $C$-closure is defined for a vertex set $S$ and uses the $(|S|+1)$-closure of the induced graph on $S$; for $S=V(C)$ we have $|S|=c$. "Two vertices" in the definition of Hamiltonian-connected is read as two distinct vertices; the Hamiltonian path is Mathlib's `Walk.IsHamiltonian` (every vertex visited exactly once).
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 4 (§1.4, k-closure and C-closure) and p. 6 (§2.1, Hamiltonian-connected, locally maximal cycle)

import Mathlib
import Definitions.Def_CircStability_Main_Setting

namespace CircStability.Main

open Finset SimpleGraph

open Classical in
/-- `H` is `k`-closed: every pair of distinct non-adjacent vertices has degree sum `< k`. -/
def IsKClosed {V : Type*} [Fintype V] (k : ℕ) (H : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → ¬ H.Adj u v → H.degree u + H.degree v < k

/-- The `k`-closure of `G` (p. 4): the least `k`-closed supergraph of `G`, which is the result of
recursively joining non-adjacent pairs with degree sum at least `k`. -/
noncomputable def kClosure {V : Type*} [Fintype V] (k : ℕ) (G : SimpleGraph V) : SimpleGraph V :=
  sInf {H | G ≤ H ∧ IsKClosed k H}

/-- The `C`-closure `Ḡ` (p. 4) for `S = V(C)`: `G` with the induced subgraph `G[S]` replaced by its
`(|S| + 1)`-closure (degrees taken in `G[S]`). For a cycle `C` of length `c`, `|S| = c`. -/
noncomputable def cClosure {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∨ ∃ (hu : u ∈ S) (hv : v ∈ S),
    (kClosure (#S + 1) (G.induce (S : Set (Fin n)))).Adj ⟨u, hu⟩ ⟨v, hv⟩
  symm := ⟨fun u v h => by
    rcases h with h | ⟨hu, hv, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hv, hu, h.symm⟩⟩
  loopless := ⟨fun u h => by
    rcases h with h | ⟨hu, _, h⟩
    · exact G.loopless.irrefl u h
    · exact (SimpleGraph.loopless _).irrefl _ h⟩

open Classical in
/-- `C` is locally maximal in `G` (§2.1, p. 6): `C` is a cycle and every strictly longer cycle `D`
of `G` has more than two edges between `V(C)` and `V(G) ∖ V(C)`. -/
def IsLocallyMaximal {n : ℕ} (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u) : Prop :=
  C.IsCycle ∧ ∀ (v : Fin n) (D : G.Walk v v), D.IsCycle → C.length < D.length →
    2 < (D.edges.filter (fun e => ∃ x ∈ e, ∃ y ∈ e, x ∈ C.support ∧ y ∉ C.support)).length

/-- Hamiltonian-connected (§2.1, p. 6): every two distinct vertices are the ends of a path through
every vertex. -/
def HamConnected {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ p : H.Walk x y, p.IsHamiltonian

end CircStability.Main


