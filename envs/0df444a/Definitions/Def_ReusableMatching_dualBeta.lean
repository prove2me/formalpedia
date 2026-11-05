-- Prove2me | Definitions.Def_ReusableMatching_dualBeta
-- name    : ReusableMatching_dualBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:01.579196+00:00
-- url     : https://prove2.me/theorems/e60cf3f9-88da-4d40-bd98-28668d0e3dcd
-- title:
--   The random dual variable $\beta_j(Y)$, eq. (1)
-- statement:
--   For a seed vector $Y$ and an arrival $j$, if Periodic Reranking matches $j$ to resource $i$, then
--
--   $$
--   \beta_j(Y)=r_i\bigl(1-g(y_i^{k(j)})\bigr),
--   $$
--
--   the reduced price of $i$ at $j$; if $j$ is unmatched, $\beta_j(Y)=0$. The dual of the analysis is $\beta_j=\mathbb E_Y[\beta_j(Y)]$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §3.1 Dual construction, eq. (1), p.8

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **The random dual variable `β_j(Y)`** of the analysis of Periodic Reranking
(arXiv:2110.07084v2, §3.1 "Dual construction", p.8, eq. (1)): "Initialize all dual variables to 0.
Conditioned on `Y`, for each match `(i, j)` in PR set of assigned edge, let
`β_j(Y) = r_i (1 − g(y_i^{k(j)}))`."

So `β_j(Y)` is the reduced price of the resource matched to `j`, and `0` if `j` is unmatched. -/
noncomputable def dualBeta {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (j : Fin n) : ℝ :=
  (PeriodicReranking I β Y j).elim 0 (fun i => reducedPrice I β Y i j)

end ReusableMatching


