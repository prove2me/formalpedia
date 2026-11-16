-- Prove2me | Definitions.Def_VertexSampleCSP_Supplement_maxCutOn
-- name    : VertexSampleCSP_Supplement_maxCutOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:59:10.932202+00:00
-- url     : https://prove2.me/theorems/64279c97-b7d6-4c90-b2eb-c41eefbfe9a9
-- title:
--   Max cut $\mathrm{mc}(G[S])$, edge count $m_S$, density $\kappa(G[S])$ and $R(G)=\sum_v\sqrt{d_v}$
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, and for $S\subseteq V$ let $G[S]$ be the induced subgraph.
--
--   1. The **maximum cut** $\mathrm{mc}(G[S])$ is the largest number of edges of $G[S]$ crossing a bipartition $(T,S\setminus T)$ of $S$.
--   2. $m_S$ is the number of edges of $G$ with both ends in $S$.
--   3. The **max-cut density** is $\kappa(G[S])=\mathrm{mc}(G[S])/m_S$, with $\kappa=0$ when $G[S]$ has no edge.
--   4. $R(G)=\sum_{v\in V}\sqrt{d_v}$, with $d_v$ the degree of $v$ (so $\Gamma(G)=\sqrt2\,R(G)$ is the scale of the Max-Cut instance of $G$).
--
--   With $S=V$ these are $\mathrm{mc}(G)$, $m$ and $\kappa(G)$; with $S$ a random vertex set they describe the vertex percolation $G_p=G[S]$ of Theorem D.5.
--
--   **Formalization Note** The induced subgraph is not built as a separate graph: its edges are the edges of $G$ inside $S$. A crossing edge is counted once, as an ordered pair from $T$ to $S\setminus T$. The density uses real division, whose value $0/0=0$ is exactly the convention $\kappa=0$ for edgeless graphs.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.3 (PDF p.5); Appendix A, "Instances", p.13 (PDF p.15); Lemma D.4 and Theorem D.5, pp.19–20 (PDF pp.21–22)

import Mathlib

namespace VertexSampleCSP.Supplement

/-- The number of edges of `G` from `T` to `S \ T`: ordered pairs `(u, v)` with `u ∈ T`, `v ∈ S`,
`v ∉ T` and `u v` an edge. Each edge of `G[S]` crossing the bipartition `(T, S \ T)` is counted
once. -/
def cutSize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) : ℕ :=
  ((T ×ˢ (S \ T)).filter (fun p => G.Adj p.1 p.2)).card

/-- **Maximum cut `mc(G[S])` of the induced subgraph on `S`.** Chang, *Optimal Vertex Sampling for
Constraint Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.3
(PDF p.5): "mc(G) is the maximum number of edges crossing a bipartition"; Theorem D.5, p.20
(PDF p.22), applied to `G_p = G[S]`.

`maxCutOn G S = max_{T ⊆ S} |{edges of G[S] with one end in T and one in S \ T}|`.

**Formalization Note.** The induced subgraph `G[S]` is not built as a separate graph: its edges are
the edges of `G` with both ends in `S`, and a bipartition of `S` is `(T, S \ T)` with `T ⊆ S`. The
maximum over the nonempty finite family `S.powerset` is a `Finset.sup` in `ℕ`. -/
def maxCutOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  S.powerset.sup (fun T => cutSize G S T)

/-- **Number of edges `m_S` of the induced subgraph `G[S]`.** Chang, STOC 2027 submission
(manuscript sha256 1e0edd23…), Lemma D.4 and Theorem D.5, p.19–20 (PDF pp.21–22): the edges of `G`
with both ends in `S`. -/
def edgesOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).card

/-- **Max-cut density `κ(G[S]) = mc(G[S]) / m_S`.** Chang, STOC 2027 submission (manuscript sha256
1e0edd23…), §1.1, p.3 (PDF p.5): "the max-cut density κ(G) = mc(G)/m … (and κ = 0 for edgeless
graphs)".

**Formalization Note.** When `G[S]` has no edge, `m_S = 0` and the real division gives `0 / 0 = 0`,
which is exactly the paper's convention `κ = 0` for edgeless graphs. -/
noncomputable def kappaOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  (maxCutOn G S : ℝ) / (edgesOn G S : ℝ)

/-- **`R(G) = Σ_v √d_v`.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A,
"Instances", p.13 (PDF p.15): "For Max-Cut of a graph, q = 2 and fe(a, b) = 1[a ≠ b] on the edges,
so γv = √2 dv and Γ(G) = √2 R(G) with R(G) = Σ_v √dv." Here `√2 dv` is `√(2 d_v)`; `R(G)` is the
sum over all vertices of the square root of the degree (isolated vertices contribute `0`). -/
noncomputable def degSqrtSum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ v, Real.sqrt (G.degree v : ℝ)

end VertexSampleCSP.Supplement


