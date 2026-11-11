-- Prove2me | Definitions.Def_MinorFreeSTC_Main_Graphs
-- name    : MinorFreeSTC_Main_Graphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:16:47.442201+00:00
-- url     : https://prove2.me/theorems/0a2ea308-2ca6-4189-ab54-6d1a74fc7bde
-- title:
--   Weighted graphs: connectedness, K_r-minor-freeness, aspect ratio, strong diameter and radius, balls, partitions, H_n and κ_r (§3, §4)
-- statement:
--   Let $G=(V,E,w)$ be a finite weighted graph: $V$ a finite set, $E$ a set of unordered pairs of distinct vertices and $w:E\to\mathbb R_{>0}$ (the published `WGraph`). The **length** of a walk is the sum of its edge weights with multiplicity; $d_G(u,v)\in[0,\infty]$ is the least length of a $u$–$v$ walk ($\infty$ if there is none), and for $A\subseteq V$, $d_A(u,v)=d_{G[A]}(u,v)$ is the same in the induced subgraph.
--
--   * $G$ is **connected** if $d_G(u,v)<\infty$ for all $u,v$; it is **$K_r$-minor-free** if its underlying simple graph has no $K_r$ minor ($r$ pairwise disjoint nonempty connected branch sets, pairwise joined by an edge); it is **unweighted** if every edge has weight $1$; it has **aspect ratio bounded by $n^k$** if $1\le w(e)\le n^k$ for every edge, $n=|V|$.
--   * The **strong diameter** of $A\subseteq V$ is $\operatorname{diam}(A)=\max_{u,v\in A}d_A(u,v)$ (so a cluster of finite strong diameter induces a connected subgraph); the **strong radius** about $c$ is $\operatorname{rad}(A,c)=\max_{v\in A}d_A(c,v)$; $\operatorname{diam}(G)=\max_{u,v}d_G(u,v)$.
--   * $d_G(v,A)=\min_{u\in A}d_G(v,u)$, $d_G(A,A')=\min_{u\in A,u'\in A'}d_G(u,u')$, closed balls $B_G(v,R)=\{u: d_G(u,v)\le R\}$ and $B_G(A,R)=\{v: d_G(v,A)\le R\}$. A **shortest path** is a path of length $d_G(u,v)$.
--   * $H_n=\lceil\log_2 n\rceil+1$ and $\kappa_r=5\binom r2(r-3)$.
--   * A **partition** of $V$ is a set of nonempty clusters with every vertex in exactly one; a **partial partition** has nonempty pairwise disjoint clusters that need not cover $V$. It is **$\Delta$-diameter** if every cluster has strong diameter at most $\Delta$; $\mathcal Q$ **coarsens** $\mathcal P$ if every cluster of $\mathcal P$ lies in one of $\mathcal Q$.
--   * Auxiliary encodings used by the machine layouts: the partition into the fibres of a labelling $L:V\to\mathbb R$, the partial partition into the fibres of its nonnegative labels, and the cluster of $\mathcal P$ containing $v$.
--
--   **Formalization Note.** Distances live in $[0,\infty]$; a bound "$\le\Delta$" is `≤ ENNReal.ofReal Δ`. Clusters are `Finset V`, partitions `Finset (Finset V)`. Logarithms are `Real.logb 2`.
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), pp. 13–14 (§3.1–3.2), p. 16 (H_n), p. 17 (κ_r, Theorem 6), p. 1 (K_r-minor-free)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HadwigerConj_Defs

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-!
# Weighted graphs: connectedness, minor-freeness, aspect ratio, strong diameter, balls, partitions

Filtser, Fletcher, Hershkowitz, Milenković, *(1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free
Graphs with Size O(log log n)*, STOC 2027 submission (manuscript sha256 f475e254…), §3.1–3.2,
pp. 13–14 (PDF 15–16), and §4, p. 16 (PDF 18).

* The weighted graph `G = (V, E, w)` is the published `ARTreeCover.WGraph V` (a `SimpleGraph V`
  with weights positive on edges); `G.dist u v ∈ [0, ∞]` is `d_G(u, v)` (`∞` if no path) and
  `G.distIn A u v` is `d_{G[A]}(u, v)`, the distance inside the induced subgraph.
* All logarithms are base 2 (`Real.logb 2`).
-/

variable {V : Type}

/-- `G` is connected (p. 14): `d_G(u, v) < ∞` for all `u, v`. -/
def Connected (G : WGraph V) : Prop := ∀ u v : V, G.dist u v < ⊤

/-- `G` is `K_r`-minor-free: its underlying simple graph has no `K_r` minor (branch sets). -/
def MinorFree (G : WGraph V) (r : ℕ) : Prop := ¬ HadwigerConj.HasCompleteMinor G.graph r

/-- `G` is unweighted: every edge has weight `1`. -/
def Unweighted (G : WGraph V) : Prop := ∀ e ∈ G.graph.edgeSet, G.w e = 1

/-- Polynomial aspect ratio (p. 13): `w(e) ∈ [1, n^k]` for every edge `e`, `n = |V|`. -/
def AspectBounded [Fintype V] (G : WGraph V) (k : ℕ) : Prop :=
  ∀ e ∈ G.graph.edgeSet, 1 ≤ G.w e ∧ G.w e ≤ (Fintype.card V : ℝ) ^ k

/-- The strong diameter `diam(A) = max_{u, v ∈ A} d_{G[A]}(u, v)` of a vertex set `A`, in `[0, ∞]`
(`∞` when `G[A]` is disconnected; `0` for the empty set). -/
noncomputable def sdiam (G : WGraph V) (A : Set V) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, G.distIn A u v

/-- The strong radius `rad(A, c) = max_{v ∈ A} d_A(c, v)` of `A` about `c`. -/
noncomputable def srad (G : WGraph V) (A : Set V) (c : V) : ℝ≥0∞ :=
  ⨆ v ∈ A, G.distIn A c v

/-- The diameter `diam(G) = max_{u, v} d_G(u, v)`. -/
noncomputable def diamG (G : WGraph V) : ℝ≥0∞ := ⨆ u : V, ⨆ v : V, G.dist u v

/-- `d_G(v, A) = min_{u ∈ A} d_G(v, u)`. -/
noncomputable def distToSet (G : WGraph V) (v : V) (A : Set V) : ℝ≥0∞ := ⨅ u ∈ A, G.dist v u

/-- `d_G(A, A') = min_{u ∈ A, u' ∈ A'} d_G(u, u')`. -/
noncomputable def setDist (G : WGraph V) (A A' : Set V) : ℝ≥0∞ := ⨅ u ∈ A, ⨅ u' ∈ A', G.dist u u'

/-- `d_{G[S]}(v, A) = min_{u ∈ A} d_{G[S]}(v, u)`. -/
noncomputable def distInToSet (G : WGraph V) (S : Set V) (v : V) (A : Set V) : ℝ≥0∞ :=
  ⨅ u ∈ A, G.distIn S v u

/-- The closed ball `B_G(v, R) = {u | d_G(u, v) ≤ R}`. -/
def ball (G : WGraph V) (v : V) (R : ℝ) : Set V := {u | G.dist u v ≤ ENNReal.ofReal R}

/-- The closed ball around a set, `B_G(A, R) = {v | d_G(v, A) ≤ R}`. -/
def ballSet (G : WGraph V) (A : Set V) (R : ℝ) : Set V :=
  {v | distToSet G v A ≤ ENNReal.ofReal R}

/-- A walk `p` from `u` to `v` is a shortest path of `G`: a path of weight `d_G(u, v)`. -/
def IsShortestPath (G : WGraph V) {u v : V} (p : G.graph.Walk u v) : Prop :=
  p.IsPath ∧ G.walkWeight p = G.dist u v

/-- `H_n := ⌈log n⌉ + 1` (§4, p. 16). -/
noncomputable def Hn (n : ℕ) : ℕ := ⌈Real.logb 2 n⌉₊ + 1

/-- `κ_r := 5 · binom(r, 2) · (r − 3)` (Theorem 6, p. 17). -/
def kappa (r : ℕ) : ℕ := 5 * Nat.choose r 2 * (r - 3)

/-- A partition of `V` (p. 14): nonempty clusters, every vertex in exactly one. -/
def IsPartition (P : Finset (Finset V)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧ ∀ v : V, ∃! C, C ∈ P ∧ v ∈ C

/-- A partial partition (p. 14): nonempty, pairwise disjoint clusters, not necessarily covering. -/
def IsPartialPartition (P : Finset (Finset V)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧ ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D

/-- Every cluster has strong diameter at most `∆` (a `∆`-diameter (partial) partition). -/
def DiamLe (G : WGraph V) (P : Finset (Finset V)) (Δ : ℝ) : Prop :=
  ∀ C ∈ P, sdiam G (C : Set V) ≤ ENNReal.ofReal Δ

/-- `Q` coarsens `P`: every cluster of `P` is contained in a cluster of `Q`. -/
def Coarsens (Q P : Finset (Finset V)) : Prop := ∀ A ∈ P, ∃ B ∈ Q, A ⊆ B

open Classical in
/-- The partition of `V` into the fibres of a labelling `L : V → ℝ`. -/
noncomputable def labelPartition [Fintype V] (L : V → ℝ) : Finset (Finset V) :=
  Finset.univ.image fun v => Finset.univ.filter fun u => L u = L v

open Classical in
/-- The partial partition into the fibres of the nonnegative labels of `L` (a vertex with a
negative label is in no cluster). -/
noncomputable def labelPartial [Fintype V] (L : V → ℝ) : Finset (Finset V) :=
  (Finset.univ.filter fun v => 0 ≤ L v).image fun v => Finset.univ.filter fun u => L u = L v

open Classical in
/-- The cluster of `P` containing `v` (`∅` if there is none). -/
noncomputable def clusterOf (P : Finset (Finset V)) (v : V) : Finset V :=
  if h : ∃ C, C ∈ P ∧ v ∈ C then h.choose else ∅

end MinorFreeSTC.Main


