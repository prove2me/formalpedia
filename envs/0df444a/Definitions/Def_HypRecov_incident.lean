-- Prove2me | Definitions.Def_HypRecov_incident
-- name    : HypRecov_incident
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:27.359756+00:00
-- url     : https://prove2.me/theorems/44d83265-cf01-4828-843e-1215f535ea8a
-- title:
--   Vertices incident to a graph cut and internally vertex-disjoint paths
-- statement:
--   For a graph $J$ on $V$ and $S\subseteq V$: the **edge boundary** $\delta_J(S)$ is the set of edges with exactly one endpoint in $S$; $U_J(S)$ is the set of vertices incident to an edge of $\delta_J(S)$, and $b_J(S)=|U_J(S)|$.
--
--   Two vertices $u,v$ are joined by **$h$ internally vertex-disjoint paths** in $J$ if there are $h$ paths from $u$ to $v$ in $J$ whose vertex sets pairwise meet only in $\{u,v\}$.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Appendix D, p.37 (PDF p.38)

import Mathlib

namespace HypRecov

/-- **Vertices incident to a graph cut, `U_J(S)`.** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Appendix D, p.37
(PDF p.38): "For a graph J on V, write U_J(S) = {v ∈ V : v is incident to an edge of δ_J(S)},
b_J(S) = |U_J(S)|." -/
def incident {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ w, G.Adj v w ∧ (v ∈ S ↔ w ∉ S))

/-- The edge boundary `δ_J(S)` of a graph: the edges with exactly one endpoint in `S`. -/
def crossEdges {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Set (Sym2 (Fin n)) :=
  {x | x ∈ G.edgeSet ∧ ∃ u v : Fin n, x = s(u, v) ∧ u ∈ S ∧ v ∉ S}

/-- **`h` internally vertex-disjoint `u`–`v` paths** (ibid., Lemma D.2, p.37): `h` paths from `u` to
`v` in `G` whose vertex sets pairwise meet only in `{u, v}`. -/
def IntDisjointPaths {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (h : ℕ) : Prop :=
  ∃ p : Fin h → G.Walk u v, (∀ i, (p i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ w ∈ (p i).support, w ∈ (p j).support → w = u ∨ w = v

end HypRecov


