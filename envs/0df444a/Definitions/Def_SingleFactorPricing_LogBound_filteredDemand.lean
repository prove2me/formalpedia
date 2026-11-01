-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
-- name    : SingleFactorPricing_LogBound_filteredDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:43.160517+00:00
-- url     : https://prove2.me/theorems/f1c4127a-74d3-425e-b8d7-88933602c197
-- title:
--   Filtered demand $G(q)$
-- statement:
--   For $q\ge0$,
--
--   $$
--   G(q)=\int\sum_{i\in N}f_i\,d_{t,i}(\bar p_t)\,\delta_{t,i}(q)\,d\mu(t),
--   $$
--
--   which for finitely many types is the paper's $G(q)=\sum_{j\in M}\theta_j\sum_{i\in N}f_id_{ij}(\bar p^j)\delta_{ij}(q)$. It is the $f$-weighted demand at the personalized optimal solution, filtering out the pairs $(i,t)$ with $\bar p_{t,i}<qf_i$, so pairs are dropped as $q$ grows.
--
--   **Formalization Note** Integrability in the type is a hypothesis of the statements that need it (`TypeRegularity`).
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.3

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeFilteredDemand

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The filtered demand** `G(q)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.3:
"`G(q) := ∑_{j∈M} θ_j ∑_{i∈N} f_i d_ij(p̄ʲ) δ_ij(q)   q ≥ 0.`"

**Formalization Note.** The sum over `M` weighted by `θ` is `∫ … dμ(t)`; the definition is total in
`q`. Integrability in `t` is a hypothesis of the statements that use it (`TypeRegularity`). -/
noncomputable def filteredDemand {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) (q : ℝ) : ℝ :=
  ∫ t, typeFilteredDemand d f pbar t q ∂μ

end SingleFactorPricing.LogBound


