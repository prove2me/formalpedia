-- Prove2me | Definitions.Def_PathCount2k_Graph
-- name    : PathCount2k_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:45.30793+00:00
-- url     : https://prove2.me/theorems/310110ab-8acc-40b4-926c-6a84b8353d4c
-- title:
--   §2.1, p.4 and Def. 2.18, p.14 — directed $k$-vertex paths $\mathcal P_k$, the count $N$, walks $W_p(v)$
-- statement:
--   Let $G=(V,E)$ be a directed graph with vertex set $V=\{0,\dots,n-1\}$ and arc set $E\subseteq V\times V$, so $m=|E|$. A **directed $k$-vertex path** is a sequence $P=(v_1,\dots,v_k)$ of pairwise distinct vertices with $(v_i,v_{i+1})\in E$ for every $i<k$; $\mathcal P_k$ is the set of these paths and $N=|\mathcal P_k|$ is their number. A **walk** of length $p-1$ is a sequence $(v_1,\dots,v_p)$ with $(v_i,v_{i+1})\in E$ for every $i<p$, vertices allowed to repeat; $W_p(v)$ is the set of walks of length $p-1$ ending at $v$.
--
--   These are the objects counted in Theorem 1.1 and aggregated by the dynamic program of §2.10.
--
--   **Formalization Note** Vertices are `Fin n`, arcs a `Finset (Fin n × Fin n)` (self-loops allowed; a path never uses one), positions are 0-based (`Fin k`).
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §2.1, p.4; Definition 2.18, p.14

import Mathlib

namespace PathCount2k

/-- **Directed `k`-vertex paths.** Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time
O\*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027
submission manuscript (Nov 2026), §2.1, p.4: "A walk of length `k − 1` is an ordered sequence
`(v₁, …, v_k)` satisfying `(vᵢ, vᵢ₊₁) ∈ E` for every `i < k`. It is a path if its vertices are
pairwise distinct. Let `P_k` denote the set of these paths".

`paths n E k` is the set of maps `P : Fin k → Fin n` that are injective and satisfy
`(P i, P (i+1)) ∈ E` whenever `i + 1 < k`.

**Formalization Note.** The host graph `G = (V, E)` has vertex set `Fin n` and arc set
`E : Finset (Fin n × Fin n)`, so `m = E.card`; self-loops `(v, v) ∈ E` are allowed (a path never
uses one). Positions are 0-based: the paper's `vᵢ` is `P ⟨i − 1, _⟩`. -/
def paths (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter fun P =>
    Function.Injective P ∧ ∀ (i : Fin k) (h : i.val + 1 < k), (P i, P ⟨i.val + 1, h⟩) ∈ E

/-- **The path count** `N = |P_k|`, §2.1, p.4. -/
def N (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ) : ℕ := (paths n E k).card

/-- **Walks ending at a vertex**, `W_p(v)` of Definition 2.18, p.14: "Let `W_p(v)` be the set of
walks of length `p − 1` ending at `v`". A walk `W : Fin p → Fin n` satisfies `(W i, W (i+1)) ∈ E`
whenever `i + 1 < p`; it ends at `v` when its last vertex `W ⟨p − 1, _⟩` is `v`.

**Formalization Note.** Vertices may repeat. For `p = 0` the end condition is vacuous; the paper
only uses `p ∈ [k]`, `p ≥ 1`. -/
def walksTo (n : ℕ) (E : Finset (Fin n × Fin n)) (p : ℕ) (v : Fin n) : Finset (Fin p → Fin n) :=
  Finset.univ.filter fun W =>
    (∀ (i : Fin p) (h : i.val + 1 < p), (W i, W ⟨i.val + 1, h⟩) ∈ E) ∧
      ∀ h : 0 < p, W ⟨p - 1, by omega⟩ = v

end PathCount2k


