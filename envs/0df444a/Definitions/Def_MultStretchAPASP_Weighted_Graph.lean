-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_Graph
-- name    : MultStretchAPASP_Weighted_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:08:41.694441+00:00
-- url     : https://prove2.me/theorems/3f0fd9cc-cdc8-48fc-862b-dd0f48c61f44
-- title:
--   Weighted undirected graphs on Fin n, the distance δ(u, v) in [0, ∞], δ(u, S), pivots and the edge set E_S
-- statement:
--   A weighted undirected graph on the vertices $0,1,\dots,n-1$ is given by its weight matrix $w:\{0,\dots,n-1\}^2\to[0,\infty]$: $w(x,y)\in[0,\infty)$ is the weight of the edge $\{x,y\}$ and $w(x,y)=\infty$ means that there is no edge. The graph is undirected and has no loops: $w(x,y)=w(y,x)$ and $w(x,x)=\infty$. In §5 every edge weight is moreover a positive integer at most $W_{\max}$.
--
--   The weight of a walk $\langle y_0,\dots,y_\ell\rangle$ is $\sum_{i=1}^{\ell} w(y_{i-1},y_i)$, and the **distance** is
--   $$\delta(u,v)=\inf\{\text{weight of a walk from }u\text{ to }v\}\in[0,\infty],$$
--   so $\delta(u,u)=0$ and $\delta(u,v)=\infty$ exactly when no walk joins $u$ and $v$. For a vertex set $S$, $\delta(u,S)=\min_{s\in S}\delta(u,s)$ with $\delta(u,\emptyset)=\infty$. A **pivot map** for $S$ assigns to every vertex $u$ some $p(u)\in S$ with $\delta(u,p(u))=\delta(u,S)$ (ties are free). The edge set
--   $$E_S=\bigcup_{u}E_S(u),\qquad E_S(u)=\{(u,v)\in E : w(u,v)<\delta(u,S)\},$$
--   collects the edges lighter than the distance of one endpoint to $S$, and $G_S=(V,E_S,w)$ is the subgraph with these edges. These are the objects of §2.1–§2.2 on which the sampling hierarchy and Algorithm 10 are built.
--
--   **Formalization Note.** Weights and distances live in `ℝ≥0∞`; `dist w u v` is an infimum over vertex lists in `ℝ≥0∞`, so the empty infimum is `⊤ = ∞`, the paper's value for disconnected pairs, not a junk value. `edgesBelow w S` counts $E_S$ as unordered pairs; `restrictBelow w S` is the weight matrix of $G_S$.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), pp. 4–5, §2.1–§2.2

import Mathlib

set_option autoImplicit false

open scoped ENNReal Classical

namespace MultStretchAPASP.Weighted

/-!
# Weighted undirected graphs on `Fin n`, distances, pivots and the edge set `E_S`

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), §2.1 (p. 4) and §2.2 (p. 5).

* A graph on the vertex set `Fin n` is its weight matrix `w : Fin n → Fin n → ℝ≥0∞`: `w x y` is
  the weight of the edge `{x, y}` and `w x y = ⊤` means that there is no such edge. `IsWGraph w`:
  the matrix is symmetric (the graph is undirected) and `⊤` on the diagonal (no loops). Finite
  entries are the non-negative real weights of §2.1 ("w : E → ℝ≥0").
* `IsIntWGraph Wmax w`: §5's standing assumption (p. 19): every edge weight is a positive
  integer in `[Wmax] = {1, …, Wmax}`.
* `walkWt w l`: the weight of the walk visiting the vertices of the list `l` in order (the sum
  of the weights of consecutive pairs; `0` for a walk with one vertex).
* `dist w u v = δ(u, v)`: the infimum, in `ℝ≥0∞`, of the weights of the walks from `u` to `v`.
  It is `0` for `u = v` (the one-vertex walk) and `⊤ = ∞` exactly when no walk joins `u` and `v`
  (no connectivity is assumed; an empty infimum in `ℝ≥0∞` is `⊤`, the paper's `∞`).
* `distSet w u S = δ(u, S) = min_{s ∈ S} δ(u, s)`, with `δ(u, ∅) = ∞` (p. 5).
* `IsPivotMap w S p`: `p u = p_S(u) ∈ S` with `δ(u, p_S(u)) = δ(u, S)` for every `u` (p. 5). Ties
  are left free: the statements quantify over every such map.
* `edgesBelow w S = E_S = ⋃_u E_S(u)`, `E_S(u) = {(u, v) ∈ E | w(u, v) < δ(u, S)}` (p. 5), as a
  set of undirected edges `s(u, v)`.
* `restrictBelow w S`: the weight matrix of `G_S = (V, E_S, w)`.
-/

/-- A weight matrix on the vertex set `Fin n`; `⊤` means "no edge". -/
abbrev WMat (n : ℕ) := Fin n → Fin n → ℝ≥0∞

/-- An undirected weighted graph without loops: a symmetric weight matrix with `⊤` on the
diagonal. -/
def IsWGraph {n : ℕ} (w : WMat n) : Prop :=
  (∀ x y : Fin n, w x y = w y x) ∧ ∀ x : Fin n, w x x = ⊤

/-- §5 (p. 19): an undirected graph whose edge weights are positive integers at most `Wmax`. -/
def IsIntWGraph {n : ℕ} (Wmax : ℕ) (w : WMat n) : Prop :=
  IsWGraph w ∧ ∀ x y : Fin n, w x y ≠ ⊤ → ∃ k : ℕ, 1 ≤ k ∧ k ≤ Wmax ∧ w x y = (k : ℝ≥0∞)

/-- The weight of the walk through the vertices of `l`, in order. -/
def walkWt {n : ℕ} (w : WMat n) : List (Fin n) → ℝ≥0∞
  | x :: y :: t => w x y + walkWt w (y :: t)
  | _ => 0

/-- `δ(u, v)`: the least weight of a walk from `u` to `v` (`⊤` if there is none). -/
noncomputable def dist {n : ℕ} (w : WMat n) (u v : Fin n) : ℝ≥0∞ :=
  ⨅ (l : List (Fin n)) (_ : l.head? = some u ∧ l.getLast? = some v), walkWt w l

/-- `δ(u, S) = min_{s ∈ S} δ(u, s)`, and `δ(u, ∅) = ⊤`. -/
noncomputable def distSet {n : ℕ} (w : WMat n) (u : Fin n) (S : Finset (Fin n)) : ℝ≥0∞ :=
  ⨅ s ∈ S, dist w u s

/-- `p` is a pivot map for `S`: `p u ∈ S` and `δ(u, p u) = δ(u, S)` for every vertex `u`. -/
def IsPivotMap {n : ℕ} (w : WMat n) (S : Finset (Fin n)) (p : Fin n → Fin n) : Prop :=
  ∀ u : Fin n, p u ∈ S ∧ dist w u (p u) = distSet w u S

/-- `E_S = ⋃_u {(u, v) ∈ E | w(u, v) < δ(u, S)}`, as undirected edges. -/
noncomputable def edgesBelow {n : ℕ} (w : WMat n) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun e => w e.1 e.2 < distSet w e.1 S).image
    fun e => s(e.1, e.2)

/-- The weight matrix of `G_S = (V, E_S, w)`: the edges of `E_S` with their weights. -/
noncomputable def restrictBelow {n : ℕ} (w : WMat n) (S : Finset (Fin n)) : WMat n :=
  fun x y => if w x y < distSet w x S ∨ w x y < distSet w y S then w x y else ⊤

end MultStretchAPASP.Weighted


