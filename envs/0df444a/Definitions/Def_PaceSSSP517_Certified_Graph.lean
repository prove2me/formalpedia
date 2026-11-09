-- Prove2me | Definitions.Def_PaceSSSP517_Certified_Graph
-- name    : PaceSSSP517_Certified_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:13.502036+00:00
-- url     : https://prove2.me/theorems/05e19cb2-d1e3-4690-86b5-efc5c81156b7
-- title:
--   Positive weighted graphs, exact local shortest paths, and PACE parameters
-- statement:
--   Let $G=(V,E,w)$ be a finite simple undirected graph. Each edge has an arbitrary positive real weight. A walk may traverse an edge in either direction, and its cost is the sum of its edge weights. Define the extended nonnegative distance by
--
--   $$\operatorname{dist}_K(u,v)=\inf\{w(P):P\text{ is a walk from }u\text{ to }v\text{ in }K\}.$$
--
--   The empty infimum is $+\infty$. Connectivity means that every pair has a finite walk. A shortest-path tree is a connected $(n-1)$-edge subgraph realizing every source distance. An $\alpha$-spanner is a connected subgraph preserving all pairwise distances within factor $\alpha$. No theorem about the PACE run is included in these definitions.
--
--   For a finite profile $d$, an edge fails if $|d(u)-d(v)|>w(e)$ and its jump is $J(e;d)=\max\{|d(u)-d(v)|-w(e),0\}/w(e)$. The source is $s_0$; the real sample budget is $s$. The admissible parameters are $k\ge2$, $0<\varepsilon<1$, $k\le\ln n$, and $12k^2\le\varepsilon n$, with
--
--   $$s=(20/\varepsilon)kn^{1+1/k}\ln n,\quad \theta=\varepsilon/(10kn^{1/k}),\quad R_{\rm wc}=\lceil11k^2/\varepsilon\rceil.$$
--
--   These definitions separate the general weighted graph from the PACE transition. Exact local distances are calculated by $n-1$ synchronous Bellman–Ford relaxations in the stored subgraph. The parent tie rule chooses the least numbered tight predecessor. Correctness, finiteness and path attainment are later proof obligations. Vertices are numbered by `Fin n`, and an edge is stored with its smaller endpoint first. Unreachable values remain extended distances; a real conversion is only used on connected subgraphs in the asserted results.
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 5, §3.1 and §3.2; p. 6, Algorithm 1 line 3; p. 17, Appendix A preamble

import Mathlib

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical

namespace PaceSSSP517.Certified

/-- The general finite simple positive-real weighted undirected graph of §3.1, p.5.
Each undirected edge is stored once, with its smaller endpoint first. -/
structure WeightedGraph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  weight : (Fin n × Fin n) → ℝ
  ordered : ∀ e ∈ edges, e.1 < e.2
  positive : ∀ e ∈ edges, 0 < weight e

abbrev Edge (n : ℕ) := Fin n × Fin n

/-- Canonical orientation only for storage; paths may traverse either direction. -/
def edge {n : ℕ} (u v : Fin n) : Edge n := if u ≤ v then (u, v) else (v, u)

def Adj {n : ℕ} (K : Finset (Edge n)) (u v : Fin n) : Prop := edge u v ∈ K

/-- A concrete finite walk including both endpoints. -/
def IsWalk {n : ℕ} (K : Finset (Edge n)) (u v : Fin n) (p : List (Fin n)) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain (Adj K)

noncomputable def pathCost {n : ℕ} (G : WeightedGraph n) (p : List (Fin n)) : ℝ :=
  ((p.zip p.tail).map (fun a => G.weight (edge a.1 a.2))).sum

/-- Genuine extended nonnegative distance: empty infimum is infinity. All uses of
`distance` below have a connected subgraph; finiteness/attainment is a proof obligation. -/
noncomputable def edistance {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (u v : Fin n) : ℝ≥0∞ :=
  ⨅ (p : List (Fin n)) (_ : IsWalk K u v p), ENNReal.ofReal (pathCost G p)

noncomputable def distance {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (u v : Fin n) : ℝ := (edistance G K u v).toReal

def Connected {n : ℕ} (K : Finset (Edge n)) : Prop :=
  ∀ u v : Fin n, ∃ p, IsWalk K u v p

/-- A shortest-path tree is a connected n-1 edge subgraph realizing the distances.
This is a specification of a local exact shortest-path calculation, not PACE's guarantee. -/
noncomputable def IsShortestTree {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (s₀ : Fin n) (T : Finset (Edge n)) : Prop :=
  T ⊆ K ∧ Connected T ∧ T.card + 1 = n ∧
    ∀ x, edistance G T s₀ x = edistance G K s₀ x

/-- Synchronous exact local shortest paths: at most n-1 relaxations in the
stored graph, with two vertex arrays, no additional stream pass. -/
noncomputable def relax {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (d : Fin n → ℝ≥0∞) (v : Fin n) : ℝ≥0∞ :=
  min (d v) (K.inf (fun e =>
    if e.1 = v then d e.2 + ENNReal.ofReal (G.weight e)
    else if e.2 = v then d e.1 + ENNReal.ofReal (G.weight e) else ⊤))

noncomputable def bellman {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (s₀ : Fin n) : ℕ → Fin n → ℝ≥0∞
  | 0 => fun v => if v = s₀ then 0 else ⊤
  | j + 1 => relax G K (bellman G K s₀ j)

noncomputable def localProfile {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (s₀ : Fin n) (v : Fin n) : ℝ := (bellman G K s₀ (n - 1) v).toReal

/-- Tie rule: least numbered tight predecessor, using only the observed subgraph.
Strictly positive edge weights orient these parent links toward the source.
The fallback s₀ is unused on connected legal subgraphs at non-source vertices. -/
noncomputable def parent {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (s₀ v : Fin n) : Fin n :=
  let d := bellman G K s₀ (n - 1)
  let candidates := Finset.univ.filter (fun u =>
    edge u v ∈ K ∧ d u + ENNReal.ofReal (G.weight (edge u v)) = d v)
  if h : candidates.Nonempty then candidates.min' h else s₀

noncomputable def shortestTree {n : ℕ} (G : WeightedGraph n) (K : Finset (Edge n))
    (s₀ : Fin n) : Finset (Edge n) :=
  (Finset.univ.erase s₀).image (fun v => edge (parent G K s₀ v) v)

/-- A spanner includes connectivity explicitly, which is redundant with its usual
all-pairs stretch definition on a connected graph, not an extra graph restriction. -/
noncomputable def IsSpanner {n : ℕ} (G : WeightedGraph n) (H : Finset (Edge n))
    (α : ℝ) : Prop :=
  H ⊆ G.edges ∧ Connected H ∧
    ∀ u v, edistance G H u v ≤ ENNReal.ofReal α * edistance G G.edges u v

noncomputable def fails {n : ℕ} (G : WeightedGraph n) (d : Fin n → ℝ) (e : Edge n) : Prop :=
  G.weight e < |d e.1 - d e.2|

noncomputable def jump {n : ℕ} (G : WeightedGraph n) (d : Fin n → ℝ) (e : Edge n) : ℝ :=
  max (|d e.1 - d e.2| - G.weight e) 0 / G.weight e

/-- Standing parameters from §3.1, p.5, without an arbitrary minimum graph size. -/
def Parameters (n k : ℕ) (ε : ℝ) : Prop :=
  2 ≤ k ∧ 0 < ε ∧ ε < 1 ∧ (k : ℝ) ≤ Real.log n ∧ 12 * (k : ℝ)^2 ≤ ε * n

noncomputable def root (n k : ℕ) : ℝ := (n : ℝ) ^ (1 / (k : ℝ))
noncomputable def budget (n k : ℕ) (ε : ℝ) : ℝ :=
  (20 / ε) * k * (n : ℝ) ^ (1 + 1 / (k : ℝ)) * Real.log n
noncomputable def theta (n k : ℕ) (ε : ℝ) : ℝ := ε / (10 * k * root n k)
noncomputable def roundCap (k : ℕ) (ε : ℝ) : ℕ := ⌈11 * (k : ℝ)^2 / ε⌉₊

end PaceSSSP517.Certified


