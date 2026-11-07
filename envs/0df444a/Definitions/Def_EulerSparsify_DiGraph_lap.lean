-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_lap
-- name    : EulerSparsify_DiGraph_lap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:10.872448+00:00
-- url     : https://prove2.me/theorems/b63b2ea2-2a20-4e6e-88ca-15f483868bf0
-- title:
--   Undirected Laplacian $L_G=B^\top WB$
-- statement:
--   Let $W=\mathrm{diag}(w)$. The **Laplacian** of the undirected graph $G=\mathrm{und}(\vec G)$ is
--
--   $$L_G = B^\top W B,$$
--
--   so that $x^\top L_G x=\sum_{e} w_e (x_{h(e)}-x_{t(e)})^2$. This is the matrix against which every spectral error in the mission is measured.
--
--   **Formalization Note** The scaling follows the paper's formula on p.10 ("For $G=\mathrm{und}(\vec G)$, we have $L_G=B^\top WB$"): weight $w_e$, not $2w_e$. (The identity $\tfrac12(\vec L+\vec L^\top)=L_G$ stated on p.1 holds with $\tfrac12 B^\top WB$; the paper's proofs use $B^\top WB$, and Theorem 1.2 is unaffected by the factor 2.) Subgraphs are encoded by zeroing weights, so every Laplacian is a $V\times V$ matrix.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Graph matrices, pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_incMat

namespace EulerSparsify

/-- The diagonal weight matrix `W = diag(w)`. -/
noncomputable def DiGraph.wMat {V E : Type} [DecidableEq E] (G : DiGraph V E) : Matrix E E ℝ :=
  Matrix.diagonal G.w

/-- **Undirected Laplacian** `L_G = BᵀWB` (§3, "Graph matrices", p.9–10, PDF pp.11–12).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.9: "For undirected
G = (V, E, w) with transfer matrix B, the Laplacian matrix of G is L := BᵀWB"; p.10: "For
G := und(⃗G), we have L_G = BᵀWB."

**Formalization Note.** `G.lap` is the Laplacian of `und(⃗G)` with the weights `w` (not `2w`), as
the paper's formula on p.10 fixes the scaling. Subgraphs are encoded by zeroing weights
(`DiGraph.restrict`, `DiGraph.unitOn`), so every Laplacian is a `V × V` matrix. -/
noncomputable def DiGraph.lap {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : DiGraph V E) : Matrix V V ℝ :=
  G.incMat.transpose * G.wMat * G.incMat

end EulerSparsify


