-- Prove2me | Definitions.Def_MatMulDS_Supplement_adjWords
-- name    : MatMulDS_Supplement_adjWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:13:44.240227+00:00
-- url     : https://prove2.me/theorems/f5b2528d-4f1d-4d80-8eed-80c76926fba6
-- title:
--   Graphs on the word RAM: adjacency lists, distances, approximations, strong LDSND
-- statement:
--   Graphs are simple, on the vertex set $V=\{0,\dots,n-1\}$, and given by **adjacency lists**: the list of $v$ holds every neighbour (for directed graphs, every out-neighbour) of $v$ exactly once, in any order; the input words are $n$, then for each $v$ the length of its list followed by the list.
--
--   - $d_G(s,v)$ is the length of a shortest $s$–$v$ path, $\infty$ if none; a table of distances on $S\times V$ stores $d_G(S_k,v)$ in word cell $kn+v$, with code $-1$ for $\infty$.
--   - For $\rho\ge1$, $\sigma\ge0$, a **$(\rho,\sigma)$-approximation** of $x\in\mathbb R_{\ge0}\cup\{\infty\}$ is any $\tilde x$ with $x\le\tilde x\le\rho x+\sigma$ (footnote 16); a $(1+\varepsilon)$-approximation is a $(1+\varepsilon,0)$-approximation.
--   - For connected $G$: $e_G(v)=\max_u d_G(u,v)$, $\operatorname{diam}(G)=\max_{u,v}d_G(u,v)$, $\operatorname{rad}(G)=\min_v e_G(v)$.
--   - For $d,\phi\ge1$, a **strong $(d,\phi)$-low diameter small neighbourhood decomposition** (Definition E.3) is a partition $\mathcal C=\{C_1,\dots,C_t\}$ of $V$ into nonempty cells with (i) $\operatorname{diam}(G[C_i])\le d$ for all $i$, the diameter of the induced subgraph, and (ii) $\sum_i|N[C_i]|\le\phi n$, where $N[C]$ is the closed neighbourhood of $C$.
--
--   **Formalization Note** The cells of a decomposition are the classes of a labelling of the vertices; (i) asks for a walk of length at most $d$ inside the cell between any two of its vertices.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §3, p.14 (PDF p.16); footnote 16, p.54 (PDF p.56); pp.60, 62 (PDF pp.62, 64); Definition E.3, p.97 (PDF p.99)

import Mathlib

set_option autoImplicit false

namespace MatMulDS.Supplement

/-- `L` is an **adjacency-list representation** of the simple graph `G` on `Fin n`: the list of `v` holds every neighbour
of `v` exactly once, in any order (§3, p.14: graphs "given by adjacency lists"). -/
def IsAdjRep {n : ℕ} (G : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)) : Prop :=
  ∀ v, (L v).Nodup ∧ ∀ u, u ∈ L v ↔ G.Adj v u

/-- **The input words of a graph given by adjacency lists** `L` (undirected: every edge in both lists; directed: the
out-neighbours): `n`, then for each vertex `v = 0, …, n − 1` the length of its list followed by the list, 0-based. -/
def adjWords {n : ℕ} (L : Fin n → List (Fin n)) : List ℤ :=
  (n : ℤ) :: (List.finRange n).flatMap fun v => ((L v).length : ℤ) :: (L v).map fun u => ((u : ℕ) : ℤ)

/-- The words of a list of vertices: its length, then the vertices, 0-based. -/
def vtxWords {n : ℕ} (S : List (Fin n)) : List ℤ := (S.length : ℤ) :: S.map fun s => ((s : ℕ) : ℤ)

/-- Reachability in the directed graph with out-neighbour lists `L`: a directed path, possibly of length zero. -/
def DiReach {n : ℕ} (L : Fin n → List (Fin n)) (s v : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ L a) s v

/-- The **distance code** of `d_G(s, v)`: the distance if `v` is reachable from `s`, and `−1` for `d_G(s, v) = ∞`. -/
noncomputable def distCode {n : ℕ} (G : SimpleGraph (Fin n)) (s v : Fin n) : ℤ :=
  open Classical in if G.Reachable s v then (G.dist s v : ℤ) else -1

/-- The word memory holds the table of distances on `S × V`: word cell `k n + v` holds the code of `d_G(S_k, v)`. -/
def DistTable {n w : ℕ} (G : SimpleGraph (Fin n)) (S : List (Fin n)) (mem : ℤ → BitVec w) : Prop :=
  ∀ (k : Fin S.length) (v : Fin n), (mem ((k : ℤ) * n + (v : ℕ))).toInt = distCode G S[k] v

/-- **(ρ, σ)-approximation** (footnote 16, p.54) of a distance code: `e` approximates `d` if both are `∞` (code `−1`), or
`d` is finite and `d ≤ e ≤ ρ d + σ`. -/
def ApproxCode (ρ σ : ℝ) (d e : ℤ) : Prop :=
  (d = -1 ∧ e = -1) ∨ (0 ≤ d ∧ (d : ℝ) ≤ e ∧ (e : ℝ) ≤ ρ * d + σ)

/-- **(ρ, σ)-approximation** (footnote 16, p.54) of a finite value `x`: `x ≤ e ≤ ρ x + σ`. -/
def IsApprox (ρ σ : ℝ) (x : ℕ) (e : ℝ) : Prop := (x : ℝ) ≤ e ∧ e ≤ ρ * x + σ

/-- The eccentricity `e_G(v) = max_u d_G(u, v)` (p.62), for a connected graph. -/
noncomputable def ecc {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := Finset.univ.sup fun u => G.dist v u

/-- The diameter `diam(G) = max_{u,v} d_G(u, v)` (p.60), for a connected graph. -/
noncomputable def gdiam {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := Finset.univ.sup (ecc G)

/-- The radius `rad(G) = min_u max_v d_G(u, v)` (p.60), for a connected graph with at least one vertex. -/
noncomputable def grad {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := sInf (Set.range (ecc G))

/-- The closed neighbourhood `N[C] = ⋃_{u∈C} N[u]` of a set of vertices (Definition E.3, p.97). -/
noncomputable def closedNbhd {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : Finset (Fin n) :=
  open Classical in Finset.univ.filter fun x => ∃ u ∈ C, x = u ∨ G.Adj u x

/-- **Strong (d, ϕ)-LDSND** (Definition E.3, p.97, PDF p.99), with the cells given as the classes of a labelling `lab`
(every class that occurs is a nonempty cell, and the cells partition `V`):
(i) (Low diameter) `diam(G[C_i]) ≤ d` for every cell: any two vertices of a cell are joined by a walk of length at most
`d` inside the cell, i.e. in the induced subgraph;
(ii) (Small neighbourhoods) `Σ_i |N[C_i]| ≤ ϕ n`. -/
def IsStrongLDSND {n : ℕ} (G : SimpleGraph (Fin n)) (lab : Fin n → ℕ) (d : ℕ) (ϕ : ℝ) : Prop :=
  (∀ u v : Fin n, lab u = lab v → ∃ p : G.Walk u v, p.length ≤ d ∧ ∀ x ∈ p.support, lab x = lab u) ∧
  (∑ ℓ ∈ Finset.univ.image lab,
      ((closedNbhd G (Finset.univ.filter fun v => lab v = ℓ)).card : ℝ)) ≤ ϕ * n

/-- The graph on `Fin n` whose edges are the pairs of the list `es` (loops are dropped). -/
def edgesGraph {n : ℕ} (es : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ es, e = s(p.1, p.2)}

end MatMulDS.Supplement


