-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_AssumptionA1
-- name    : SingleFactorPricing_LogBound_AssumptionA1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:42.465218+00:00
-- url     : https://prove2.me/theorems/376aaf11-725d-4402-94f9-68c9611c64e7
-- title:
--   Assumption A1
-- statement:
--   Assumption 1 of the paper is
--
--   $$
--   G(q)\le H(q)\qquad\text{for all }q\ge0.
--   $$
--
--   The left side accumulates the $f$-weighted demands at the personalized optima for the pairs with $\bar p_{t,i}\ge qf_i$; the right side is the $f$-weighted demand over all products and types at the price vector $qf$. It is the paper's main assumption and a real restriction on the demand system.
--
--   **Formalization Note** $G$ depends on the selection `pbar`.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_factorDemand

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Assumption 1.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4:
"Assumption 1 (A1): `G(q) ≤ H(q)` for all `q ≥ 0`."

**Formalization Note.** `G` depends on the selection `pbar` of optimal prices. -/
def AssumptionA1 {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) : Prop :=
  ∀ q : ℝ, 0 ≤ q → filteredDemand μ d f pbar q ≤ factorDemand μ d f q

end SingleFactorPricing.LogBound


