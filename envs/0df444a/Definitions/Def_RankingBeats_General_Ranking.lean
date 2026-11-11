-- Prove2me | Definitions.Def_RankingBeats_General_Ranking
-- name    : RankingBeats_General_Ranking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:26:39.970236+00:00
-- url     : https://prove2.me/theorems/3686f7d1-5f98-4275-b771-49d022fde2af
-- title:
--   Algorithm 1 — Ranking on a general graph with a rank vector and an initial set of removed vertices; the rank law and E_x[|R(x)|]
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $\vec x=(x_v)_{v\in V}$ a **rank vector**. **Ranking** (Algorithm 1) processes the vertices $u$ in increasing order of $x_u$; when $u$ is processed, if $u$ is available and has an available neighbour, it is matched with the available neighbour $v\in N(u)$ of smallest rank $x_v$, and both are marked unavailable. $R(\vec x)$ is the output matching. For a set $S\subseteq V$, $R(\vec x_{-S})$ is the output when the vertices of $S$ are unavailable from the start and the other ranks are unchanged (Ranking on the subgraph induced by $V\setminus S$); $R(\vec x_{-v})$ and $R(\vec x_{-uv})$ are the cases $S=\{v\}$, $S=\{u,v\}$, and $R(\vec x_{-v}(y))$ is $R$ of the vector $\vec x$ with $x_v$ replaced by $y$.
--
--   The ranks are independent and uniform on $[0,1)$; the expected output size is
--   $$\mathbb E_{\vec x}\big[|R(\vec x)|\big]=\int |R(\vec x)|\,d\Big(\bigotimes_{v\in V}\mathrm{Unif}[0,1)\Big)(\vec x).$$
--   $\Pr_{\vec x}[v\text{ is matched}]$ is the probability that $v$ is covered by $R(\vec x)$, and $\Pr[u\text{ is matched}]$ for a vertex $u$ uniform on $V$ and independent of $\vec x$ is $\sum_{v}\frac1{|V|}\Pr_{\vec x}[v\text{ is matched}]$.
--
--   This is the object of every statement of the mission: Theorem 1.1 bounds $\mathbb E[|R(\vec x)|]$ from below by $0.635\,\nu(G)$.
--
--   **Formalization Note** `ranking G S x : Finset (Sym2 V)` is $R(\vec x_{-S})$; `ranking G ∅ x` is $R(\vec x)$. The vertices are sorted by the lexicographic key `(x u, u)`, so ties of ranks (a null event, which the paper excludes W.L.O.G., p. 11) are broken by a fixed `LinearOrder V`, and a vertex picks the available neighbour of smallest key; with distinct ranks this is exactly Algorithm 1. `IsMatched M u` means $u$ lies on an edge of $M$. `rankLaw V = Measure.pi (fun _ => volume.restrict (Set.Ico 0 1))`; `expectedSize G` is the Bochner integral of the bounded function $\vec x\mapsto|R(\vec x)|$; `probMatched G v = (rankLaw V).real {x | IsMatched (ranking G ∅ x) v}`.
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 11, Algorithm 1; p. 12 (removal and insertion); p. 16 (E_x[|R(x)|], Pr[u is matched])

import Mathlib

open Classical MeasureTheory

namespace RankingBeats.General

/-!
# Algorithm 1 — Ranking on a general graph, with an initial set of removed vertices

Derakhshan, Yu, *Ranking Beats 1-1/e on General Graphs*, STOC 2027 submission (manuscript sha256
6715d477…), p. 11 Algorithm 1, p. 12 (removal and insertion notation), p. 16 (the approximation
ratio `E_x[|R(x)|] / |OPT|`).

* The vertex set is a finite type `V`; the graph is a `SimpleGraph V` (finite, no loops, no
  multi-edges), with no other condition.
* A rank vector is `x : V → ℝ`. The paper's ranks lie in `[0, 1)` and are pairwise distinct
  (W.L.O.G., p. 11); statements about a fixed rank vector carry these as hypotheses.
* Ranking processes the vertices in increasing order of rank. Ties (a null event) are broken by
  the fixed linear order `[LinearOrder V]`: vertices are sorted by the lexicographic key
  `(x u, u)`, and a vertex picks the available neighbour of smallest key. With distinct ranks the
  key order is the rank order, so the tie-break never matters.
* `ranking G S x` is the matching `R(x_{-S})`: the vertices of `S` are unavailable from the start
  and the other ranks are unchanged (Ranking on the subgraph induced by `V \ S`, p. 12).
  `R(x) = ranking G ∅ x`, `R(x_{-v}) = ranking G {v} x`, `R(x_{-uv}) = ranking G {u, v} x`, and
  the insertion `R(x_{-v}(y)) = ranking G ∅ (Function.update x v y)`.
* Edges are elements of `Sym2 V`; a matching is a `Finset (Sym2 V)`.
* `rankLaw V` is the law of i.i.d. Uniform`[0, 1)` ranks, `expectedSize G = E_x[|R(x)|]`,
  `probMatched G v = Pr_x[v is matched]`, and `probUniformVertexMatched G = Pr[u is matched]`
  for `u` uniform on `V` independent of the ranks (§5, p. 16).
-/

variable {V : Type*}

/-- The processing key of a vertex: its rank, ties broken by the fixed linear order of `V`. -/
def rankKey [LinearOrder V] (x : V → ℝ) (u : V) : ℝ ×ₗ V := toLex (x u, u)

/-- The vertices of `V` in increasing order of rank (line 2 of Algorithm 1). -/
noncomputable def processingOrder [Fintype V] [LinearOrder V] (x : V → ℝ) : List V :=
  ((Finset.univ.image (rankKey x)).sort (· ≤ ·)).map fun p => (ofLex p).2

/-- The state of a run: the available vertices and the matching built so far. -/
structure RunState (V : Type*) where
  avail : Finset V
  matching : Finset (Sym2 V)

/-- One iteration of the loop of Algorithm 1 for the vertex `u` (lines 3–5): if `u` is available
and has an available neighbour, match `u` with the available neighbour of smallest rank, and mark
both unavailable; otherwise do nothing. -/
noncomputable def step [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ) (s : RunState V) (u : V) :
    RunState V :=
  if u ∈ s.avail then
    if h : (s.avail.filter fun v => G.Adj u v).Nonempty then
      let v := (ofLex (((s.avail.filter fun v => G.Adj u v).image (rankKey x)).min'
        (h.image _))).2
      ⟨(s.avail.erase u).erase v, insert s(u, v) s.matching⟩
    else s
  else s

/-- `R(x_{-S})`: the output of Ranking (Algorithm 1) on `G` with rank vector `x`, when the vertices
of `S` are marked unavailable at the start. `R(x) = ranking G ∅ x`. -/
noncomputable def ranking [Fintype V] [LinearOrder V] (G : SimpleGraph V) (S : Finset V)
    (x : V → ℝ) : Finset (Sym2 V) :=
  ((processingOrder x).foldl (step G x) ⟨Finset.univ \ S, ∅⟩).matching

/-- `u` is matched in the edge set `M`. -/
def IsMatched (M : Finset (Sym2 V)) (u : V) : Prop := ∃ w, s(u, w) ∈ M

/-- The law of the rank vector: independent ranks, each uniform on `[0, 1)` (Algorithm 1,
line 1). -/
noncomputable def rankLaw (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  Measure.pi fun _ : V => (volume : Measure ℝ).restrict (Set.Ico 0 1)

/-- `E_x[|R(x)|]`: the expected size of the matching output by Ranking. -/
noncomputable def expectedSize [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℝ :=
  ∫ x, ((ranking G ∅ x).card : ℝ) ∂ rankLaw V

/-- `Pr_x[v is matched]` in `R(x)`, over i.i.d. Uniform`[0, 1)` ranks. -/
noncomputable def probMatched [Fintype V] [LinearOrder V] (G : SimpleGraph V) (v : V) : ℝ :=
  (rankLaw V).real {x | IsMatched (ranking G ∅ x) v}

/-- `Pr[u is matched]` for a vertex `u` drawn uniformly from `V`, independently of the ranks
(§5, p. 16): the average `∑_{v ∈ V} (1/|V|) Pr_x[v is matched]`. -/
noncomputable def probUniformVertexMatched [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℝ :=
  ∑ v, (1 / (Fintype.card V : ℝ)) * probMatched G v

end RankingBeats.General


