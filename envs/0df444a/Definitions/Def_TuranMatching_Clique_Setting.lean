-- Prove2me | Definitions.Def_TuranMatching_Clique_Setting
-- name    : TuranMatching_Clique_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:04.187037+00:00
-- url     : https://prove2.me/theorems/344f9959-2f58-4621-a6f6-54c7d21e2865
-- title:
--   p. 1 — matching number, Turán number $t(n,k)$, the graph $G(n,k,s)$ and $g(n,k,s)$, odd barriers
-- statement:
--   This file fixes the objects of Alon and Frankl's Theorem 1.1 and of its proof. All graphs are finite simple graphs.
--
--   1. **Matching number.** For a graph $G$ on a finite vertex set, $\nu(G)$ is the largest number of edges of a matching of $G$ (a set of pairwise disjoint edges).
--   2. **Turán number.** $T(n,k)$ is the complete $k$-partite graph on $n$ vertices whose classes have sizes as equal as possible (some classes are empty when $n<k$), and $t(n,k)$ is its number of edges.
--   3. **The graph $G(n,k,s)$.** On the vertex set $\{0,1,\dots,n-1\}$, the vertices $v<s$ are split into $k-1$ classes by their residue modulo $k-1$, so these classes have sizes as equal as possible and total size $s$; all vertices $v\ge s$ form one further class of size $n-s$. $G(n,k,s)$ is the complete $k$-partite graph with these classes, and $g(n,k,s)$ is its number of edges.
--   4. **Admissible graphs.** A graph is *admissible* for $(k,s)$ if its clique number is at most $k$ (it contains no complete subgraph on $k+1$ vertices) and its matching number is at most $s$.
--   5. **Odd barriers.** A vertex set $B$ of $G$ is an *odd barrier with value $s$* if every connected component $A_1,\dots,A_m$ of the graph $G-B$ (induced on the vertices outside $B$) has an odd number $a_i=|A_i|$ of vertices and
--   $$|B|+\sum_{i=1}^{m}\frac{a_i-1}{2}=s.$$
--   6. **Square sum.** For a vertex set $B$, $\sum_{i} a_i^2$ is the sum of the squared component sizes of $G-B$.
--   7. **The function of Case 4.** $f(b)=t(2s-b+1,k)+b\,(n-2s+b-1)$, an integer.
--
--   These are the objects of the paper's §1 (p. 1) and of its proof in §2 (pp. 2–4).
--
--   **Formalization Note** Vertices are `Fin n`. The matching number is the supremum (`sSup` in ℕ) of the edge counts of matching subgraphs; this set contains $0$ (the empty subgraph) and is bounded by the number of edges, so the supremum is a maximum. $T(n,k)$ is Mathlib's `turanGraph n k` (classes = residues mod $k$). $g(n,k,s)$ is the edge count of the graph $G(n,k,s)$ itself, not a closed formula. The construction of $G(n,k,s)$ is meant for $k\ge2$ and $s\le n$, as in the paper; outside that range the class map degenerates. The relation $b+\sum a_i=n$ of p. 2 holds automatically and is not part of the barrier predicate. In $f(b)$ the argument $2s-b+1$ uses natural subtraction and is meaningful for $b\le 2s$.
-- source:
--   Alon and Frankl, Turán graphs with bounded matching number, arXiv:2210.15076v1, p. 1, §1 (definitions of clique number, matching number, T(n,k), t(n,k), G(n,k,s), g(n,k,s)); p. 2, §2 (the set B); p. 4, Case 4 (f(b))

import Mathlib

namespace TuranMatching.Clique

open Finset SimpleGraph

/-- The matching number ν(G): the largest number of edges of a matching subgraph of `G`.
The set is nonempty (the empty subgraph is a matching) and bounded by the number of edges,
so the supremum is a maximum. -/
noncomputable def matchingNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m}

/-- t(n, k): the number of edges of the Turán graph T(n, k) (Mathlib's `turanGraph n k`,
the complete k-partite graph on `Fin n` with classes given by the residues mod k). -/
def turanNum (n k : ℕ) : ℕ := #(turanGraph n k).edgeFinset

/-- The class of a vertex in G(n, k, s): a vertex `v < s` lies in class `v mod (k − 1)`
(so the first s vertices form k − 1 classes of sizes as equal as possible), and every
vertex `v ≥ s` lies in the extra class `k − 1`. -/
def bigClass (k s : ℕ) {n : ℕ} (v : Fin n) : ℕ :=
  if (v : ℕ) < s then (v : ℕ) % (k - 1) else k - 1

/-- G(n, k, s): the complete k-partite graph on `Fin n` whose classes are given by `bigClass`:
k − 1 balanced classes of total size s and one class of size n − s. -/
def bigGraph (n k s : ℕ) : SimpleGraph (Fin n) where
  Adj v w := bigClass k s v ≠ bigClass k s w

instance (n k s : ℕ) : DecidableRel (bigGraph n k s).Adj :=
  inferInstanceAs (DecidableRel fun v w : Fin n ↦ bigClass k s v ≠ bigClass k s w)

/-- g(n, k, s): the number of edges of G(n, k, s). -/
def gNum (n k s : ℕ) : ℕ := #(bigGraph n k s).edgeFinset

/-- The property of Theorem 1.1: clique number at most k (no clique on k + 1 vertices) and
matching number at most s. -/
def Admissible {V : Type*} [Fintype V] (k s : ℕ) (G : SimpleGraph V) : Prop :=
  G.CliqueFree (k + 1) ∧ matchingNumber G ≤ s

/-- `B` is an odd barrier with value `s` (§2, p. 2): every connected component of the induced
graph G − B on the complement of `B` has an odd number of vertices, and
|B| + Σ_i (|A_i| − 1)/2 = s, the sum running over the components A_i of G − B. -/
def IsOddBarrier {V : Type*} [Fintype V] (G : SimpleGraph V) (B : Finset V) (s : ℕ) : Prop :=
  (∀ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, Odd c.supp.ncard) ∧
  #B + ∑ᶠ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, (c.supp.ncard - 1) / 2 = s

/-- Σ_i a_i²: the sum of the squared sizes of the connected components of G − B. -/
noncomputable def compSqSum {V : Type*} [Fintype V] (G : SimpleGraph V) (B : Finset V) : ℕ :=
  ∑ᶠ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, c.supp.ncard ^ 2

/-- The function of Case 4 (§2, p. 4): f(b) = t(2s − b + 1, k) + b(n − 2s + b − 1), computed in ℤ
(the Turán term uses natural subtraction 2s − b, meaningful for b ≤ 2s). -/
def fCase4 (n k s b : ℕ) : ℤ :=
  (turanNum (2 * s - b + 1) k : ℤ) + (b : ℤ) * ((n : ℤ) - 2 * s + b - 1)

end TuranMatching.Clique


