-- Prove2me | Definitions.Def_DirKECC1549_Main_Supplement_Undirected
-- name    : DirKECC1549_Main_Supplement_Undirected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:16:20.541311+00:00
-- url     : https://prove2.me/theorems/967be2fc-6b08-4c3c-8e23-5b7ccf55caf0
-- title:
--   k-vertex-connected components of undirected graphs, C_k(G), ‖C_k(G)‖ and the graph J_k
-- statement:
--   Let $G$ be a simple undirected graph on $V=\{0,\dots,n-1\}$.
--
--   1. Two vertices $u,v$ are **$k$-vertex-connected** (§6.5, p.33) if they cannot be separated by fewer than $k$ vertices distinct from $u$ and $v$: for every $X\subseteq V\setminus\{u,v\}$ with $|X|<k$, some walk from $u$ to $v$ avoids $X$. Adjacent vertices, and $u=v$, are $k$-vertex-connected for every $k$.
--   2. A **$k$-vertex-connected component** is a nonempty inclusion-maximal set of pairwise $k$-vertex-connected vertices (no lower bound on its cardinality). $C_k(G)$ is the family of these components and
--   $$\|C_k(G)\|=\sum_{K\in C_k(G)}|K|$$
--   is their total size.
--   3. **The graph $J_k$** (§6.5.2, p.35, Figure 3). Let $\ell=\lfloor (k-1)/3\rfloor$ and $h=k+2-3\ell$. $J_k$ has $k+2$ vertices: a set $U$ of $3\ell$ vertices partitioned into triples $P_0,\dots,P_{\ell-1}$, with every edge between different triples and none inside a triple, and a set $B$ of $h$ pairwise non-adjacent vertices, each adjacent to every vertex of $U$.
--
--   These are the objects of the paper's bounds on the number and total size of $k$-vertex-connected components (Theorems 9 and 10).
--
--   **Formalization Note** $J_k$ has vertex set $\{0,\dots,k+1\}$: the vertex $3i+j$ ($i<\ell$, $j<3$) is $x_{i,j}\in P_i$, so a vertex $a<3\ell$ lies in the triple $P_{\lfloor a/3\rfloor}$; the vertices $3\ell,\dots,k+1$ form $B$. Natural-number subtraction in $\ell$ and $h$ is exact for $k\ge1$ and $k\ge 3\ell-2$, which always holds.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), §6.5 p.33 (definitions, C_k(G), ‖·‖), §6.5.2 p.35 and Figure 3 (the graph J_k)

import Mathlib

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main.Supplement

/-!
# k-vertex-connected components of undirected graphs and the graph `J_k` (§6.5, pp.33–35)
-/

variable {n : ℕ}

/-- `u` and `v` are joined in `G − X`: a walk from `u` to `v` none of whose vertices lies in `X`. -/
def UReachAvoid (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u v : Fin n) : Prop :=
  ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ X

/-- Undirected `k`-vertex-connectivity (§6.5, p.33): `u` and `v` cannot be separated by fewer than
`k` vertices distinct from `u` and `v`. Adjacent vertices, and `u = v`, are `k`-vertex-connected for
every `k`. -/
def UKVertexConnected (k : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  ∀ X : Finset (Fin n), u ∉ X → v ∉ X → X.card < k → UReachAvoid G X u v

/-- The vertices of `S` are pairwise `k`-vertex-connected in the undirected graph `G`. -/
def UPairwiseKVC (k : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, UKVertexConnected k G u v

/-- A `k`-vertex-connected component of an undirected graph (p.33): a nonempty inclusion-maximal
set of pairwise `k`-vertex-connected vertices, with no lower bound on its cardinality. -/
def IsUKVCC (k : ℕ) (G : SimpleGraph (Fin n)) (K : Finset (Fin n)) : Prop :=
  K.Nonempty ∧ UPairwiseKVC k G K ∧ ∀ K' : Finset (Fin n), K ⊆ K' → UPairwiseKVC k G K' → K' = K

/-- The family `C_k(G)` of the `k`-vertex-connected components of `G` (p.33). -/
def kvccFamily (k : ℕ) (G : SimpleGraph (Fin n)) : Finset (Finset (Fin n)) :=
  univ.filter (fun K => IsUKVCC k G K)

/-- The total size `‖C_k(G)‖ = ∑_{K ∈ C_k(G)} |K|` (p.33). -/
def kvccTotalSize (k : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ K ∈ kvccFamily k G, K.card

/-! ## The graph `J_k` (§6.5.2, p.35, Figure 3)

`ℓ = ⌊(k − 1)/3⌋`, `h = k + 2 − 3ℓ`. The vertex set is `Fin (k + 2)`: vertices `0, …, 3ℓ − 1` form
`U`, the vertex `3i + j` (`j < 3`) being `x_{i,j}` of the triple `P_i`; vertices `3ℓ, …, k + 1` form
`B = {b_1, …, b_h}`. -/

/-- `ℓ = ⌊(k − 1)/3⌋`. -/
def ell (k : ℕ) : ℕ := (k - 1) / 3

/-- `h = k + 2 − 3ℓ`. -/
def hB (k : ℕ) : ℕ := k + 2 - 3 * ell k

/-- `J_k`: every edge between vertices of `U` in different triples, no edge inside a triple, every
vertex of `B` adjacent to every vertex of `U`, no edge inside `B`. -/
def Jk (k : ℕ) : SimpleGraph (Fin (k + 2)) :=
  SimpleGraph.fromRel (fun a b : Fin (k + 2) =>
    ((a : ℕ) < 3 * ell k ∧ (b : ℕ) < 3 * ell k ∧ (a : ℕ) / 3 ≠ (b : ℕ) / 3) ∨
    ((a : ℕ) < 3 * ell k ∧ 3 * ell k ≤ (b : ℕ)))

end DirKECC1549.Main.Supplement


