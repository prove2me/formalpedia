-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_filterIndicator
-- name    : SingleFactorPricing_LogBound_filterIndicator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:56.896009+00:00
-- url     : https://prove2.me/theorems/8947ef5e-1927-498e-97d1-59acc9c4946b
-- title:
--   The filter $\delta_{ij}(q)$
-- statement:
--   For a product $i$, a type $t$ and $q\in\mathbb R$,
--
--   $$
--   \delta_{t,i}(q)=\begin{cases}1,&q\le\bar p_{t,i}/f_i,\\0,&\text{otherwise.}\end{cases}
--   $$
--
--   It records whether the pair $(i,t)$ survives at level $q$ of the pricing direction $f$: the pair is kept while the price $qf_i$ does not exceed its personalized optimal price.
--
--   **Formalization Note** The inequality is non-strict, as printed.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.3

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The filter** `δ_ij(q)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.3: "Define
`δ_ij(q) := 1` if `q ≤ p̄_ij/f_i` and `δ_ij(q) := 0` otherwise."

**Formalization Note.** The inequality is non-strict, as printed. -/
noncomputable def filterIndicator {N T : Type*} (f : N → ℝ) (pbar : T → N → ℝ) (t : T) (i : N)
    (q : ℝ) : ℝ :=
  if q ≤ pbar t i / f i then 1 else 0

end SingleFactorPricing.LogBound


