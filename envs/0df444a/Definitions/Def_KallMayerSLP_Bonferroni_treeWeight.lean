-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_treeWeight
-- name    : KallMayerSLP_Bonferroni_treeWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:04.700997+00:00
-- url     : https://prove2.me/theorems/06234c98-d4c8-400b-9809-643c3eaa8247
-- title:
--   Weight $w(T)$ of a subgraph of the complete graph
-- statement:
--   Let $G$ be the complete graph on the vertices $1,\dots,r$ with edge weights $(i,j)\mapsto\mathbb P(B_i\cap B_j)$. The weight of a subgraph $T$ is the sum over its edges,
--   $$
--   w(T)=\sum_{(i,j)\in E_T}\mathbb P(B_i\cap B_j).
--   $$
--
--   **Formalization Note** Each undirected edge is listed once, as the pair $(i,j)$ with $i<j$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, p.290 (PDF 299)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.Bonferroni

open Classical in
/-- The weight `w(T) = ∑_{(i,j) ∈ E_T} ℙ(B_i ∩ B_j)` of a subgraph `T` of the complete graph on the
vertices `0, …, r-1`, for the edge weights `(i, j) ↦ ℙ(B_i ∩ B_j)`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, §3.4, p.290 (PDF 299).

**Formalization Note.** Each undirected edge `{i, j}` of `T` is listed exactly once, as the pair
`(i, j)` with `i < j`. -/
noncomputable def treeWeight {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {r : ℕ}
    (B : Fin r → Set Ω) (T : SimpleGraph (Fin r)) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2 ∧ T.Adj p.1 p.2),
    μ.real (B p.1 ∩ B p.2)

end KallMayerSLP.Bonferroni


