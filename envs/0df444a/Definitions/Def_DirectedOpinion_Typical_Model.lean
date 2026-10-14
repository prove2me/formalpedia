-- Prove2me | Definitions.Def_DirectedOpinion_Typical_Model
-- name    : DirectedOpinion_Typical_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:06.88998+00:00
-- url     : https://prove2.me/theorems/38ab96a3-a576-42b4-97a8-1961602e708e
-- title:
--   pp. 3, 21–24 — weighted directed graph, operator Δ (10), opinion recursion (1), time-reversed sums B^(k) and the stationary vector Σ_r Δ^r W^(r)
-- statement:
--   A **vertex-weighted directed (multi)graph** $G$ on a vertex set $V$ is given by ordered lists of inbound neighbours: vertex $i$ has in-degree $d_i^-\in\mathbb N$, its $r$-th inbound neighbour is $\ell(i,r)\in V$, and $c(i,r)$ is the weight (trust) that $i$ places on it, $1\le r\le d_i^-$. The graph is **valid for $c$** if every weight lies in $[0,1]$ and
--   $$\sum_{r=1}^{d_i^-}c(i,r)=c\qquad\text{for every } i \text{ with } d_i^->0 .$$
--   It is **locally finite** if every vertex also has finite out-degree $d_i^+$. The **signal budget** of $i$ is $d+c-\sum_{r=1}^{d_i^-}c(i,r)$.
--
--   For parameters $c,d$ the operator (10) acts on functions $f:V\to\mathbb R$ by
--   $$\Delta f(i)=\sum_{r=1}^{d_i^-}c(i,r)\,f(\ell(i,r))+(1-c-d)\,f(i).$$
--   Given an initial vector $R^{(0)}$ and signals $W^{(k)}=(W_i^{(k)})_{i\in V}$, $k\ge0$, the **opinion process** of recursion (1) is
--   $$R_i^{(k+1)}=\sum_{r=1}^{d_i^-}c(i,r)\,R^{(k)}_{\ell(i,r)}+W_i^{(k)}+(1-c-d)R_i^{(k)},\qquad\text{i.e. } R^{(k+1)}=\Delta R^{(k)}+W^{(k)} .$$
--   The **time-reversed partial sums** are $B^{(k)}=\sum_{r=0}^{k}\Delta^rW^{(r)}$, and the **stationary vector** is
--   $$R=\sum_{r=0}^{\infty}\Delta^rW^{(r)} .$$
--
--   These are the objects of Theorem 1 and of the proofs of Theorems 1, 2 and 7; on a random graph they are evaluated on each realization.
--
--   **Formalization Note** Neighbour indices are 0-based: `nbr i r` and `wt i r` for `r < deg i` are the paper's $\ell(i,r+1)$ and $c(i,r+1)$; values for `r ≥ deg i` are never read. Signals are indexed by time $k\ge0$, as in (1). The stationary vector is a `tsum`; for signals bounded by the budget and $d>0$ the family is absolutely summable, since $|\Delta^r f|\le(1-d)^r\sup|f|$.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 3 (recursion (1), weight condition), p. 4 (signal bound), p. 5 (Theorem 1, locally finite), pp. 21–23 ((10), proof of Theorem 1), p. 24 (B^(k)), p. 27 (R = Σ Δ̄^r W^(r))

import Mathlib

namespace DirectedOpinion.Typical

/-- A vertex-weighted directed (multi)graph given by ordered in-neighbour lists (p. 3):
`deg i` is the in-degree `d_i⁻`, `nbr i r` is `ℓ(i, r+1)`, the `(r+1)`-th inbound neighbour of `i`,
and `wt i r` is `c(i, r+1)`, the weight `i` places on it. Indices are 0-based: only `r < deg i`
is meaningful, and the values of `nbr i r`, `wt i r` for `r ≥ deg i` are never read. -/
structure WDigraph (V : Type*) where
  deg : V → ℕ
  nbr : V → ℕ → V
  wt : V → ℕ → ℝ

/-- Standing weight conditions (p. 3; the mark space `[0,1]^∞` of p. 3 puts each weight in `[0,1]`):
every weight lies in `[0, 1]`, and the weights of a vertex with `d_i⁻ > 0` sum to `c`. -/
def WDigraph.Valid {V : Type*} (G : WDigraph V) (c : ℝ) : Prop :=
  (∀ i r, r < G.deg i → 0 ≤ G.wt i r ∧ G.wt i r ≤ 1) ∧
    ∀ i, 0 < G.deg i → ∑ r ∈ Finset.range (G.deg i), G.wt i r = c

/-- Local finiteness (Theorem 1, `d_i⁻ + d_i⁺ < ∞`): in-degrees are finite by construction, and
every vertex `j` is an inbound neighbour of only finitely many (vertex, slot) pairs, so its
out-degree `d_j⁺` is finite. -/
def WDigraph.LocallyFinite {V : Type*} (G : WDigraph V) : Prop :=
  ∀ j : V, Set.Finite {p : V × ℕ | p.2 < G.deg p.1 ∧ G.nbr p.1 p.2 = j}

/-- The signal budget `d + c − Σ_{r=1}^{d_i⁻} c(i, r)` of vertex `i` (p. 4): the bound on
`|W_i^(k)|`. It equals `d` when `d_i⁻ > 0` and `c + d` when `d_i⁻ = 0`. -/
def WDigraph.budget {V : Type*} (G : WDigraph V) (c d : ℝ) (i : V) : ℝ :=
  d + c - ∑ r ∈ Finset.range (G.deg i), G.wt i r

/-- The operator (10), p. 21: `Δf(i) = Σ_{r=1}^{d_i⁻} c(i, r) f(ℓ(i, r)) + (1 − c − d) f(i)`. -/
def Δ {V : Type*} (G : WDigraph V) (c d : ℝ) (f : V → ℝ) (i : V) : ℝ :=
  ∑ r ∈ Finset.range (G.deg i), G.wt i r * f (G.nbr i r) + (1 - c - d) * f i

/-- The opinion process of recursion (1), p. 3: `R^(0) = R0` and
`R_i^(k+1) = Σ_r c(i, r) R_{ℓ(i,r)}^(k) + W_i^(k) + (1 − c − d) R_i^(k)`, i.e.
`R^(k+1) = Δ R^(k) + W^(k)`. Signals are indexed by time `k ≥ 0`. -/
def opinion {V : Type*} (G : WDigraph V) (c d : ℝ) (R0 : V → ℝ) (W : ℕ → V → ℝ) :
    ℕ → V → ℝ
  | 0 => R0
  | k + 1 => fun i => Δ G c d (opinion G c d R0 W k) i + W k i

/-- The time-reversed process `B^(k) = Σ_{r=0}^{k} Δ^r W^(r)` (p. 24). -/
def revPartial {V : Type*} (G : WDigraph V) (c d : ℝ) (W : ℕ → V → ℝ) (k : ℕ) (i : V) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), (Δ G c d)^[r] (W r) i

/-- The stationary vector `R = Σ_{r ≥ 0} Δ^r W^(r)` (proof of Theorem 1, p. 23, where
`R = B̃ − 1`; proof of Theorem 2, p. 27). For signals bounded by the budget and `d > 0` the series
is absolutely summable, since `|Δ^r f| ≤ (1 − d)^r sup |f|`. -/
noncomputable def stationary {V : Type*} (G : WDigraph V) (c d : ℝ) (W : ℕ → V → ℝ) (i : V) : ℝ :=
  ∑' r : ℕ, (Δ G c d)^[r] (W r) i

end DirectedOpinion.Typical


