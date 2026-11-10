-- Prove2me | Definitions.Def_RevRedSAT_VCInstance
-- name    : RevRedSAT_VCInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:50.555788+00:00
-- url     : https://prove2.me/theorems/69d00b1e-89d1-4c75-a5f3-4b4c8f35f0a4
-- title:
--   Vertex Cover instances, vertex covers and their codes
-- statement:
--   **Vertex Cover** (App. C.1, p.92): given a finite simple undirected graph $G$ and a budget $k\ge0$, find a set $S\subseteq V(G)$ with $|S|\le k$ such that every edge has an endpoint in $S$. The parameter is $k$.
--
--   An instance is a triple $(n,G,k)$ with vertex set $\{0,\dots,n-1\}$; $S$ is a **vertex cover** if every edge $uv$ has $u\in S$ or $v\in S$, and the feasible solutions are the vertex covers of size at most $k$. For a vertex set $V'$, a set $S$ **covers the induced subgraph** $G[V']$ if every edge of $G$ with both endpoints in $V'$ has an endpoint in $S$.
--
--   A **code** of the instance is $n$, then the list of the edges, each edge exactly once and in either orientation, then $k$, every number in self-delimiting binary. Every listing order and orientation gives a code, and every statement of the mission holds for all codes.
--
--   **Formalization Note** The graph is a `SimpleGraph (Fin n)`; $n=0$ is allowed.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92 (Vertex Cover); App. C, p.92 (graphs finite, simple, undirected); §3, p.27 (explicit encodings)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_SearchWithin

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- **An instance of Vertex Cover.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92: "Vertex
Cover. Given a graph G and a budget k, find a set S ⊆ V(G) of size at most k such that every edge
has an endpoint in S. The parameter is k (Theorem 5.3)"; App. C, p.92: "Unless stated otherwise,
graphs are finite, simple, undirected, and unweighted"; "Budgets … are nonnegative integers".

**Formalization Note** The vertex set is `Fin n` (relabelling changes no instance); `n = 0` is
allowed. -/
structure VCInstance where
  /-- the number of vertices -/
  n : ℕ
  /-- the finite simple undirected graph `G` on the vertices `0, …, n − 1` -/
  G : SimpleGraph (Fin n)
  /-- the budget `k` -/
  k : ℕ

/-- `S` is a vertex cover of `G`: every edge has an endpoint in `S`. -/
def IsVertexCover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

/-- The feasible solutions of a Vertex Cover instance: vertex covers of size at most `k`. -/
def VCValid (I : VCInstance) (S : Finset (Fin I.n)) : Prop :=
  IsVertexCover I.G S ∧ S.card ≤ I.k

/-- `S` is a vertex cover of the induced subgraph `G[V']`: every edge of `G` with both endpoints in
`V'` has an endpoint in `S`. -/
def CoversInduced {n : ℕ} (G : SimpleGraph (Fin n)) (V' S : Finset (Fin n)) : Prop :=
  ∀ u v, u ∈ V' → v ∈ V' → G.Adj u v → u ∈ S ∨ v ∈ S

/-- The code of an edge listed as the ordered pair `(u, v)`. -/
def encEdge {n : ℕ} (e : Fin n × Fin n) : List Bool := encFin e.1 ++ encFin e.2

/-- **The codes of a Vertex Cover instance** (§3, p.27, "the explicit binary encodings of an
instance"): `n`, then the list of the edges, each edge exactly once and in either orientation, then
`k`, every number in self-delimiting binary. Every listing order and every orientation gives a code;
statements quantify over all codes. -/
def IsVCCode (I : VCInstance) (w : List Bool) : Prop :=
  ∃ L : List (Fin I.n × Fin I.n),
    (L.map fun e => Sym2.mk e).Nodup ∧ (∀ e ∈ L, I.G.Adj e.1 e.2) ∧
    (∀ u v, I.G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) ∧
    w = encNat I.n ++ encList encEdge L ++ encNat I.k

end RevRedSAT


