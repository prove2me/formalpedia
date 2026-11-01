-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_personalizedProfit
-- name    : SingleFactorPricing_LogBound_personalizedProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:18.617156+00:00
-- url     : https://prove2.me/theorems/548a0043-e73f-44e4-abca-5c93bef192c7
-- title:
--   Optimal personalized profit $\bar{\mathcal R}$
-- statement:
--   Let $\bar p_t$ be an optimal price vector for type $t$. The **optimal personalized profit** is
--
--   $$
--   \bar{\mathcal R}=\int R_t(\bar p_t)\,d\mu(t).
--   $$
--
--   For finitely many types this is the paper's $\bar{\mathcal R}=\sum_{j\in M}\theta_j\mathcal R_j^*$, the profit of third-degree price discrimination, and $\mathcal R^*_t=R_t(\bar p_t)$ because $\bar p_t$ is optimal.
--
--   **Formalization Note** The definition takes the selection `pbar` as an argument; its optimality is `AssumptionA0`.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.2

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeProfit

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Optimal personalized profit** `R̄`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.2:
"Then `R̄ := ∑_{j∈M} θ_j R*_j` is the optimal profit from personalized pricing".

**Formalization Note.** `pbar t` is an optimal price vector of type `t`, so `R*_t` is
`typeProfit d t (pbar t)` once `AssumptionA0 d pbar` holds. The sum over `M` is `∫ … dμ(t)`. -/
noncomputable def personalizedProfit {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (pbar : T → N → ℝ) : ℝ :=
  ∫ t, typeProfit d t (pbar t) ∂μ

end SingleFactorPricing.LogBound


