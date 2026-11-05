-- Prove2me | Definitions.Def_ReusableMatching_g
-- name    : ReusableMatching_g
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:47.664135+00:00
-- url     : https://prove2.me/theorems/1788b88f-d2ba-4172-b2aa-ace2278a081a
-- title:
--   The trade-off function $g(x)=e^{\beta(x-1)}$
-- statement:
--   For a parameter $\beta$, the **trade-off function** of Periodic Reranking is
--
--   $$
--   g(x)=e^{\beta(x-1)}.
--   $$
--
--   For $\beta>0$ it is strictly increasing with $g(1)=1$, so a resource with seed $y\in[0,1]$ has reduced price $r_i(1-g(y))\in[0,\,r_i(1-e^{-\beta})]$; a small seed means a high priority.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Algorithm 1, p.8

import Mathlib

namespace ReusableMatching

/-- **The trade-off function** `g(x) = e^{β(x − 1)}` of Periodic Reranking (arXiv:2110.07084v2,
Algorithm 1, p.8: "Let `g(x) = e^{β(x−1)}`"; "we consider the family of functions
`g(x) = e^{β(x−1)}` parameterized by `β > 0`", p.8).

For `β > 0` it is strictly increasing, with `g(1) = 1`, so the reduced price `r_i (1 − g(y_i))` of
a resource with seed `y_i ∈ [0, 1]` lies in `[0, r_i (1 − e^{−β})]`. -/
noncomputable def g (β x : ℝ) : ℝ :=
  Real.exp (β * (x - 1))

end ReusableMatching


