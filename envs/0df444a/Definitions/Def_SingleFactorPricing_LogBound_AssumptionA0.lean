-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_AssumptionA0
-- name    : SingleFactorPricing_LogBound_AssumptionA0
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:28.370906+00:00
-- url     : https://prove2.me/theorems/0b6e5030-f047-4acc-8c91-59510b67907a
-- title:
--   Assumption A0, with optimality of $\bar p$
-- statement:
--   Assumption 0 of the paper says that optimal prices are positive and finite. In a formal statement this has two parts, for every type $t$:
--
--   1. every component $\bar p_{t,i}$ is positive, and
--   2. $\bar p_t$ is optimal for type $t$: $R_t(p)\le R_t(\bar p_t)$ for every $p\ge0$.
--
--   This fixes the selection of optimal prices against which $q_{\min}$, $q_{\max}$, $G$ and A1 are read. Optimal prices may be non-unique, and every result holds for each selection.
--
--   **Formalization Note** Finiteness is automatic in $\mathbb R$.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, pp.2–3

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeProfit

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Assumption 0, with the optimality of `p̄`.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.3:
"Assumption 0 (A0): We assume that optimal prices are positive and finite." and "Let `p̄_ij`,
`i ∈ N` is a vector of optimal prices for `R_j(p)`, `j ∈ M`."

**Formalization Note.** Finiteness is automatic in `ℝ`. Optimality is over `p ≥ 0`, from
`R*_j := max_{p≥0} R_j(p)` (p.2). Since `p̄` may be non-unique, every statement holds for each
selection `pbar`. -/
def AssumptionA0 {N T : Type*} [Fintype N] (d : T → (N → ℝ) → N → ℝ) (pbar : T → N → ℝ) : Prop :=
  ∀ t, (∀ i, 0 < pbar t i) ∧
    ∀ p : N → ℝ, (∀ i, 0 ≤ p i) → typeProfit d t p ≤ typeProfit d t (pbar t)

end SingleFactorPricing.LogBound


