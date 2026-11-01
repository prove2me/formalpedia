-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_typeFilteredDemand
-- name    : SingleFactorPricing_LogBound_typeFilteredDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:15:51.619249+00:00
-- url     : https://prove2.me/theorems/fee10487-0a8f-4177-aefb-f57b00cf8af4
-- title:
--   Type-level filtered demand $G_j(q)$
-- statement:
--   For a type $t$ and $q\ge0$,
--
--   $$
--   G_t(q)=\sum_{i\in N}f_i\,d_{t,i}(\bar p_t)\,\delta_{t,i}(q).
--   $$
--
--   This is the $f$-weighted demand of type $t$ at its personalized optimum, keeping only the products whose optimal price is at least $qf_i$.
--
--   **Formalization Note** The Lean definition is total in $q$; statements restrict $q$ as the paper does.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_filterIndicator

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The type-level filtered demand** `G_j(q)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4:
"define `G_j(q) := ∑_{i∈N} f_i d_ij(p̄ʲ)δ_ij(q)` for `q ≥ 0`".

**Formalization Note.** The definition is total in `q`; statements restrict `q` as the paper does. -/
noncomputable def typeFilteredDemand {N T : Type*} [Fintype N] (d : T → (N → ℝ) → N → ℝ)
    (f : N → ℝ) (pbar : T → N → ℝ) (t : T) (q : ℝ) : ℝ :=
  ∑ i, f i * d t (pbar t) i * filterIndicator f pbar t i q

end SingleFactorPricing.LogBound


