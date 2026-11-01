-- Prove2me | Definitions.Def_SingleFactorPricing_LogBound_TypeRegularity
-- name    : SingleFactorPricing_LogBound_TypeRegularity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:56.34261+00:00
-- url     : https://prove2.me/theorems/b770c348-aaab-4609-a180-e075f040d902
-- title:
--   Regularity in the customer type
-- statement:
--   For a general type space, the statements need three regularity properties:
--
--   1. each price $t\mapsto\bar p_{t,i}$ is measurable;
--   2. each demand $t\mapsto d_{t,i}(\bar p_t)$ at the personalized optimum is $\mu$-integrable;
--   3. each demand $t\mapsto d_{t,i}(qf)$, $q\ge0$, is $\mu$-integrable.
--
--   For finitely many types all three are automatic, so they exclude no instance of the paper's sums.
--
--   **Formalization Note** Without them, the Bochner integrals in $\bar{\mathcal R}$, $G$ and $H$ take the junk value $0$.
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.5 (remark on continuous customer types)

import Mathlib

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **Regularity in the type**, needed for a general type space. Gallego, Berbeglia,
arXiv:2102.03038v2, §2, p.5: "We remark that Theorem 1 also holds for continuous customer types".

**Formalization Note.** Measurability of `t ↦ p̄_t,i` and integrability of the demands. The paper
writes finite sums, where these are automatic. Without them the Bochner integrals in `R̄`, `G`, `H`
are `0` by convention, so they exclude no instance of the paper and rule out only junk values. -/
structure TypeRegularity {N T : Type*} [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) : Prop where
  /-- The optimal prices depend measurably on the type. -/
  measurable_price : ∀ i, Measurable fun t => pbar t i
  /-- The demand at the personalized optimum is integrable in the type. -/
  integrable_optimal : ∀ i, Integrable (fun t => d t (pbar t) i) μ
  /-- The demand at each price vector `qf`, `q ≥ 0`, is integrable in the type. -/
  integrable_factor : ∀ q : ℝ, 0 ≤ q → ∀ i, Integrable (fun t => d t (q • f) i) μ

end SingleFactorPricing.LogBound


