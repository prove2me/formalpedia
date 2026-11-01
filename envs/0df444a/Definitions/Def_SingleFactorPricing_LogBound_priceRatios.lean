-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_priceRatios
-- name    : SingleFactorPricing_LogBound_priceRatios
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:58.710592+00:00
-- url     : https://prove2.me/theorems/de0e17f8-fe58-41b9-ab0c-4e253c0658a3
-- title:
--   The ratios $\bar p_{ij}/f_i$
-- statement:
--   The set of ratios
--
--   $$
--   \{\bar p_{t,i}/f_i : t\in T,\ i\in N\},
--   $$
--
--   whose infimum and supremum are the paper's $q_{\min}=\min_{i,j}\bar p_{ij}/f_i$ and $q_{\max}=\max_{i,j}\bar p_{ij}/f_i$. The spread $q_{\max}/q_{\min}$ measures how far the personalized optimal prices are from a multiple of $f$.
--
--   **Formalization Note** Statements fix $q_{\min},q_{\max}$ through `IsGLB` and `IsLUB` of this set. For finitely many types these are the printed min and max.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The ratios** `p̄_ij/f_i` over which `q_min` and `q_max` are taken. Gallego, Berbeglia,
arXiv:2102.03038v2, §2, p.4: "`q_min := min_{i∈N,j∈M} p̄_ij/f_i` and
`q_max := max_{i∈N,j∈M} p̄_ij/f_i`."

**Formalization Note.** Statements take `q_min` and `q_max` through `IsGLB (priceRatios f pbar)`
and `IsLUB (priceRatios f pbar)`. For finitely many types these are the printed min and max. For a
general type space they express the remark on p.5, "as long as `q_min` is bounded away from zero
and `q_max` is finite". -/
def priceRatios {N T : Type*} (f : N → ℝ) (pbar : T → N → ℝ) : Set ℝ :=
  Set.range fun x : T × N => pbar x.1 x.2 / f x.2

end SingleFactorPricing.LogBound


