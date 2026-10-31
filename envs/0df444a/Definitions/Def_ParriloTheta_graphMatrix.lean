-- Prove2me | Definitions.Def_ParriloTheta_graphMatrix
-- name    : ParriloTheta_graphMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:19.176962+00:00
-- url     : https://prove2.me/theorems/a123a01e-2cf8-454c-9b9c-db31be3f2d0c
-- title:
--   Graph matrix $M_G=\alpha(G)(A_G+I)-J$
-- statement:
--   For a graph $G=(V,E)$ with stability number $\alpha(G)$, adjacency matrix $A_G$, identity $I$ and all-ones matrix $J$, the **graph matrix** is
--   $$
--   M_G=\alpha(G)\,(A_G+I)-J .
--   $$
--   Its entries are $\alpha(G)-1$ on the diagonal and at edges, and $-1$ at non-edges. By the Motzkin–Straus theorem $M_G$ is copositive, and the question studied in the paper is in which cone $\mathcal K^{(r)}$ it lies.
--
--   **Formalization Note** $\alpha(G)$ is `G.indepNum`; $A_G$ is `G.adjMatrix ℝ` with classical decidability of adjacency.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eq. (1.2), p.1

import Mathlib

namespace ParriloTheta

open Classical in
/-- **The graph matrix `M_G = α(G)(A_G + I) − J`.**
Laurent & Vargas, arXiv:2109.12876v1, eq. (1.2), p.1: "MG := α(G)(AG + I) − J", where `A_G`,
`I`, `J` are the adjacency, identity and all-ones matrices and `α(G)` is the stability number.

Its entries are `α(G) − 1` on the diagonal and on edges, and `−1` on non-edges.

**Formalization Note.** `α(G)` is Mathlib's `G.indepNum`; `A_G` is `G.adjMatrix ℝ`, built with
classical decidability of adjacency (the value does not depend on the instance). -/
noncomputable def graphMatrix {V : Type*} (G : SimpleGraph V) : Matrix V V ℝ :=
  (G.indepNum : ℝ) • (G.adjMatrix ℝ + 1) - Matrix.of (fun _ _ => (1 : ℝ))

end ParriloTheta


