-- Prove2me | Definitions.Def_MNLStability_choiceRatio
-- name    : MNLStability_choiceRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:55.442372+00:00
-- url     : https://prove2.me/theorems/da55def9-7780-49f3-b7ab-1329fd071156
-- title:
--   The ratio $\mathbb I[a\in S^m]/w(S^m)$ of Lemma 13
-- statement:
--   After customer $m$, let $S^m$ be the set of products still in stock together with the no-purchase option. For a product $a$,
--
--   $$\frac{\mathbb I[a\in S^m]}{w(S^m)},\qquad w(S^m)=w_0+\sum_{i\in S^m,\,i\ne0}w_i,$$
--
--   is $1/w(S^m)$ when $a$ is still in stock and $0$ otherwise. It is a function of the outcome $(X,X_0)$ of the demand process and of the initial vector $U$; the weights in the denominator are the ones passed to it (in Lemma 13, always the original weights $w$).
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 13, p.31; App. A.8, pp.48–49

import Mathlib
import Definitions.Def_MNLStability_Weights
import Definitions.Def_MNLStability_step

namespace MNLStability

variable {n : ℕ}

/-- `I[a ∈ S^m] / w(S^m)` of SSRN:3498325, Lemma 13, p.31, as a function of the outcome `x = (X, X₀)`
after `m` customers from the initial vector `U`: `S^m` is the set of products still in stock under
`U − X` together with the no-purchase option, and `w(S^m) = w₀ + Σ_{i ∈ S^m, i ≠ 0} w_i` is computed
with the weights `wts` passed here. -/
noncomputable def choiceRatio (wts : Weights n) (U : Fin n → ℕ) (a : Fin n)
    (x : (Fin n → ℕ) × ℕ) : ℝ :=
  if 0 < (U - x.1) a then 1 / (wts.w0 + wts.wsum (inStock (U - x.1))) else 0

end MNLStability


