-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_aggregateProfit
-- name    : SingleFactorPricing_LogBound_aggregateProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:11.658348+00:00
-- url     : https://prove2.me/theorems/f52d8157-26a0-400d-b8c2-7986febaf7db
-- title:
--   Aggregate profit $R(p)$
-- statement:
--   Let $\mu$ be the distribution of customer types. The **aggregate profit** at a single price vector $p$, charged to all types, is
--
--   $$
--   R(p)=\int R_t(p)\,d\mu(t).
--   $$
--
--   For finitely many types with weights $\theta_j$ this is the paper's $R(p)=\sum_{j\in M}\theta_jR_j(p)$. It is the profit of any non-personalized policy.
--
--   **Formalization Note** The finite sum is the integral against the published finite law `KallMayerSLP.ICC.discreteLaw θ id`, which is $\\sum_j\\theta_j\\delta_j$.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.2

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeProfit

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Aggregate profit** `R(p)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.2:
"Let `R(p) := ∑_{j∈M} θ_j R_j(p)` be the profit over all types at price `p`."

**Formalization Note.** The type distribution is a measure `μ` on the type space `T`, so the sum
over `M` weighted by `θ` becomes `∫ R_t(p) dμ(t)`. For finitely many types with weights `θ`, take
`μ = KallMayerSLP.ICC.discreteLaw θ id`, which is `∑ⱼ θⱼ • δⱼ`. -/
noncomputable def aggregateProfit {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (p : N → ℝ) : ℝ :=
  ∫ t, typeProfit d t p ∂μ

end SingleFactorPricing.LogBound


