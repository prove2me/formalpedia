-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_factorDemand
-- name    : SingleFactorPricing_LogBound_factorDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:58.735446+00:00
-- url     : https://prove2.me/theorems/373f09a6-4c6e-4187-933b-e601bcad1370
-- title:
--   Demand along the factor $H(q)$
-- statement:
--   For $q\ge0$,
--
--   $$
--   H(q)=\int\sum_{i\in N}f_i\,d_{t,i}(qf)\,d\mu(t),
--   $$
--
--   which for finitely many types is the paper's $H(q)=\sum_{j\in M}\theta_j\sum_{i\in N}f_id_{ij}(qf)$. It is the $f$-weighted demand at the single price vector $qf$.
--
--   **Formalization Note** $qf$ is `q • f`.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.3

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **The `f`-weighted demand along `f`** `H(q)`. Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.3:
"`H(q) := ∑_{j∈M} θ_j ∑_{i∈N} f_i d_ij(qf)`".

**Formalization Note.** The sum over `M` weighted by `θ` is `∫ … dμ(t)`; `qf` is `q • f`. -/
noncomputable def factorDemand {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (q : ℝ) : ℝ :=
  ∫ t, ∑ i, f i * d t (q • f) i ∂μ

end SingleFactorPricing.LogBound


