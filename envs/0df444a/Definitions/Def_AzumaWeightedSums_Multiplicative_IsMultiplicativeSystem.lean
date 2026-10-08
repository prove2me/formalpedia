-- Prove2me | Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
-- name    : AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:26.075986+00:00
-- url     : https://prove2.me/theorems/55e97bed-f7d6-483f-bf2a-45a06c8e58d1
-- title:
--   Class [M] with unit bounds: a multiplicative system
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and let $x_1,x_2,\ldots$ be real random variables. The sequence belongs to Azuma's class **[M] with unit bounds** when every $x_n$ is measurable, $|x_n|\le 1$ almost surely, and every nonempty product of variables with distinct indices has mean zero:
--
--   $$
--   E\!\left[\prod_{i\in S}x_i\right]=0
--   \qquad\text{for every nonempty finite }S\subseteq\{1,2,\ldots\}.
--   $$
--
--   Singleton sets are included, so each $x_n$ is centered. The condition also covers products of three or more variables; it is the dependence assumption behind Lemma 1 and Theorem 1.
--
--   **Formalization Note** Indices start at one; the value of $x_0$ is unused. Bounds hold almost surely for each index, as on the source page.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 357, §1, property [M], https://doi.org/10.2748/tmj/1178243286

import Mathlib

namespace AzumaWeightedSums.Multiplicative

open MeasureTheory

/-- Azuma (1967), p. 357, property [M] with `Kₙ = 1`. The sequence is indexed from
one; `x 0` is unused. The moment condition includes singleton index sets. -/
    def IsMultiplicativeSystem {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (x : ℕ → Ω → ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → Measurable (x n)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ 1) ∧
  (∀ s : Finset ℕ, s.Nonempty → (∀ i ∈ s, 1 ≤ i) →
    ∫ ω, ∏ i ∈ s, x i ω ∂μ = 0)

end AzumaWeightedSums.Multiplicative


