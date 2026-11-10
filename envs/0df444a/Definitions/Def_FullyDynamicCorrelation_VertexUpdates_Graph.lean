-- Prove2me | Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Graph
-- name    : FullyDynamicCorrelation_VertexUpdates_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:49:42.716275+00:00
-- url     : https://prove2.me/theorems/d11b4f86-ad32-4b76-8004-dc9c2fb7606a
-- title:
--   Signed complete graphs, sparsity, agreement, almost-cliques and the disagreement cost
-- statement:
--   A **signed complete graph** (Problem 1, pp. 11–12) is given by a finite set $V\subseteq\mathbb N$ of vertex names and its positive graph: two distinct vertices of $V$ carry a $(+)$ edge iff they are adjacent in the simple graph $E$, and a $(-)$ edge otherwise (`SGraph`, `SGraph.Adj`; edges of $E$ leaving $V$ are ignored).
--
--   - $N(v)$ is the **open** positive neighbourhood (`nbr`, empty for $v\notin V$), $N[v]=N(v)\cup\{v\}$ the **closed** one (`cnbr`), $\deg(v)=|N(v)|$ (`deg`).
--   - **$\theta$-agreement** (Definition 5, `Agree`): $|N[u]\triangle N[v]|\le\theta\max\{|N[u]|,|N[v]|\}$.
--   - **$\theta$-sparse** (Definition 4, `Sparse`): $N(v)=\emptyset$, or at least $\theta\deg(v)$ neighbours $u$ have $|N[v]\triangle N[u]|>\theta\max\{|N[u]|,|N[v]|\}$; $\theta$-dense is its negation.
--   - **$\theta$-almost-clique** (Definition 3, `IsAlmostClique`): a nonempty $K\subseteq V$ with $\Delta(K)=\max_{v\in K}|N[v]|$ (`maxCDeg`) such that every $v\in K$ has at most $\theta\Delta(K)$ non-neighbours in $K$ other than itself and at most $\theta\Delta(K)$ neighbours outside $K$, and $(1-\theta)\Delta(K)\le|K|\le(1+\theta)\Delta(K)$. Definition 7 (p. 31) calls such a set a $\theta$-dense core.
--   - **Cost** (`cost r`): the number of unordered pairs of distinct active vertices that are a $(+)$ edge separated by the "same cluster" relation $r$ or a $(-)$ edge put together by it, computed with the published `CorrClustBBC.Cautious.mistakes` on the graph induced on $V$ (`inducedGraph`). **opt** (`opt`) is the least cost over all partitions of $V$ (setoids on the active vertices); it is attained.
--   - `lg n` is $\log_2 n$.
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Problem 1 (pp. 11–12), Definitions 3–5 (pp. 14–15), Definition 7 (p. 31)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-!
# Signed complete graphs, sparsity, agreement and almost-cliques

Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), *Fully Dynamic Correlation Clustering
with Vertex Updates in Polylogarithmic Update Time*, supplied manuscript sha256
07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2: Problem 1 (pp. 11–12),
Definitions 3–5 (pp. 14–15), Definition 7 (p. 31).

A signed complete graph on a finite set `V` of named vertices is encoded by its positive
graph: `E` is a simple graph on `ℕ`, and two distinct vertices of `V` carry a `(+)` edge iff
they are `E`-adjacent; every other pair of distinct vertices of `V` carries a `(−)` edge.
Edges of `E` with an endpoint outside `V` are ignored.
-/

/-- A finite signed complete graph: the active vertex set `V` and the positive graph `E`. -/
structure SGraph where
  /-- the vertices currently in the graph -/
  V : Finset ℕ
  /-- positive adjacency (only pairs inside `V` count) -/
  E : SimpleGraph ℕ

namespace SGraph

variable (H : SGraph)

/-- `(u, v)` is a positive edge of the signed complete graph. -/
def Adj (u v : ℕ) : Prop := u ∈ H.V ∧ v ∈ H.V ∧ H.E.Adj u v

/-- Open positive neighbourhood `N(v)` (p. 11). Empty for a vertex outside `V`. -/
noncomputable def nbr (v : ℕ) : Finset ℕ := H.V.filter (fun u => H.Adj v u)

/-- Closed positive neighbourhood `N[v] = N(v) ∪ {v}` (p. 11). -/
noncomputable def cnbr (v : ℕ) : Finset ℕ := insert v (H.nbr v)

/-- Positive degree `deg(v) = |N(v)|`. -/
noncomputable def deg (v : ℕ) : ℕ := (H.nbr v).card

/-- Definition 5 (p. 15): `u` and `v` are in `θ`-agreement,
`|N[u] △ N[v]| ≤ θ · max {|N[u]|, |N[v]|}`. -/
def Agree (θ : ℝ) (u v : ℕ) : Prop :=
  (((symmDiff (H.cnbr u) (H.cnbr v)).card : ℕ) : ℝ) ≤
    θ * ((max (H.cnbr u).card (H.cnbr v).card : ℕ) : ℝ)

/-- Definition 4 (p. 14): `v` is `θ`-sparse if `N(v) = ∅`, or at least `θ · deg v` positive
neighbours `u` satisfy `|N[v] △ N[u]| > θ · max {|N[u]|, |N[v]|}`. -/
def Sparse (θ : ℝ) (v : ℕ) : Prop :=
  H.deg v = 0 ∨
    θ * (H.deg v : ℝ) ≤
      (((H.nbr v).filter (fun u =>
        θ * ((max (H.cnbr u).card (H.cnbr v).card : ℕ) : ℝ) <
          (((symmDiff (H.cnbr v) (H.cnbr u)).card : ℕ) : ℝ))).card : ℝ)

/-- `Δ(K) = max_{v ∈ K} |N[v]|`, the maximum closed degree over `K` (Definition 3). -/
noncomputable def maxCDeg (K : Finset ℕ) : ℕ := K.sup (fun v => (H.cnbr v).card)

/-- Definition 3 (p. 14): `K` is a (nonempty) `θ`-almost-clique of the current graph:
every `v ∈ K` has at most `θΔ(K)` non-neighbours inside `K` (not counting `v`) and at most
`θΔ(K)` neighbours outside `K`, and `(1 − θ)Δ(K) ≤ |K| ≤ (1 + θ)Δ(K)`. Definition 7 (p. 31)
calls such a set a `θ`-dense core. -/
def IsAlmostClique (θ : ℝ) (K : Finset ℕ) : Prop :=
  K.Nonempty ∧ K ⊆ H.V ∧
    (∀ v ∈ K, (((K \ H.cnbr v).card : ℕ) : ℝ) ≤ θ * (H.maxCDeg K : ℝ)) ∧
    (∀ v ∈ K, (((H.nbr v \ K).card : ℕ) : ℝ) ≤ θ * (H.maxCDeg K : ℝ)) ∧
    (1 - θ) * (H.maxCDeg K : ℝ) ≤ (K.card : ℝ) ∧
    (K.card : ℝ) ≤ (1 + θ) * (H.maxCDeg K : ℝ)

/-- The positive graph induced on the active vertex set, as a simple graph on the subtype. -/
def inducedGraph : SimpleGraph H.V := H.E.comap (fun x : H.V => (x : ℕ))

/-- Problem 1 (p. 12): the min-disagreement cost of the clustering whose "same cluster"
relation is `r` (positive pairs separated plus negative pairs together, each unordered pair of
distinct active vertices once), via the published `CorrClustBBC.Cautious.mistakes`. -/
noncomputable def cost (r : ℕ → ℕ → Prop) : ℕ :=
  CorrClustBBC.Cautious.mistakes H.inducedGraph (fun a b : H.V => r a.1 b.1)

/-- `opt`: the least cost of a clustering (a partition of `V`, given as a setoid on the active
vertices). The minimum is attained since there are finitely many partitions. -/
noncomputable def opt : ℕ :=
  sInf {k : ℕ | ∃ D : Setoid H.V, CorrClustBBC.Cautious.mistakes H.inducedGraph D.r = k}

end SGraph

/-- `log₂ n`, the logarithm used for degree levels and thresholds. -/
noncomputable def lg (n : ℕ) : ℝ := Real.logb 2 n

end FullyDynamicCorrelation.VertexUpdates


