-- Prove2me | Definitions.Def_ReusableMatching_dualAlpha
-- name    : ReusableMatching_dualAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:31.14955+00:00
-- url     : https://prove2.me/theorems/afeea38b-15eb-445f-8a73-cdc431c8a8ba
-- title:
--   The random dual variable $\alpha_{i,t}(Y)$, eq. (2)
-- statement:
--   For a seed vector $Y$, a resource $i$ and an arrival $t$, if Periodic Reranking matches $t$ to $i$, then
--
--   $$
--   \alpha_{i,t}(Y)=r_i\,g(y_i^{k(t)});
--   $$
--
--   otherwise $\alpha_{i,t}(Y)=0$. With (1), $\beta_t(Y)+\alpha_{i,t}(Y)=r_i$ on every matched pair. The dual of the analysis is $\alpha_{i,t}=\mathbb E_Y[\alpha_{i,t}(Y)]$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, §3.1 Dual construction, eq. (2), p.8

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **The random dual variable `α_{i,t}(Y)`** of the analysis of Periodic Reranking
(arXiv:2110.07084v2, §3.1 "Dual construction", p.8, eq. (2)): "Initialize all dual variables to 0.
Conditioned on `Y`, for each match `(i, j)` in PR set of assigned edge, let
`α_{i,j}(Y) = r_i g(y_i^{k(j)})`."

So `α_{i,t}(Y) = r_i g(y_i^{k(t)})` when PR matches arrival `t` to resource `i`, and `0`
otherwise. -/
noncomputable def dualAlpha {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (t : Fin n) : ℝ :=
  if PeriodicReranking I β Y t = some i then I.r i * g β (Y (i, period I t)) else 0

end ReusableMatching


