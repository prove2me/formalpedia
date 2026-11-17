-- Prove2me | Definitions.Def_SkipListConc_Supplement_IsMorrisChain
-- name    : SkipListConc_Supplement_IsMorrisChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:46.437933+00:00
-- url     : https://prove2.me/theorems/b79aa07d-9f8b-4f65-9b8a-e6c79b138f36
-- title:
--   Morris unit-promotion chain (Definition 2.4)
-- statement:
--   A process $(M(j))_{j\ge1}$ with values in $\{1,2,\dots\}$ is a **Morris unit-promotion chain** if $M(1)=1$ and, for $j\ge1$,
--   $$
--   M(j+1)=\begin{cases}M(j)+1 & \text{with probability } p^{M(j)} \text{ given } M(1),\dots,M(j),\\ M(j) & \text{otherwise.}\end{cases}
--   $$
--   It is the approximate counter of Morris; property (T2) compares every height trajectory with such a chain from below.
--
--   **Formalization Note** The conditional probabilities are written in multiplied form over every value $\tau$ of the past: $P(\text{past}=\tau,\ M(j+1)=\tau_j+1)=p^{\tau_j}P(\text{past}=\tau)$ and $P(\text{past}=\tau,\ M(j+1)=\tau_j)=(1-p^{\tau_j})P(\text{past}=\tau)$; this is the conditional statement on pasts of positive probability. $M(1)=1$ holds almost surely.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Definition 2.4, p.14

import Mathlib

open MeasureTheory

namespace SkipListConc.Supplement

/-- A Morris unit-promotion chain, Definition 2.4 (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), Definition 2.4, p.14), as a
property of a process `M : ℕ → Ω → ℕ` (index `j ≥ 1` = the `j`-th operation on the item):
`M(1) = 1` and, for `j ≥ 1`, `M(j+1) = M(j) + 1` with probability `p^{M(j)}` given the past,
and `M(j+1) = M(j)` otherwise.

**Formalization Note** "With probability `p^{M(j)}` given the past" is written in multiplied
form: for every past `τ` (the values `M(1), …, M(j)`),
`P(past = τ, M(j+1) = τ_j + 1) = p^{τ_j} P(past = τ)` and
`P(past = τ, M(j+1) = τ_j) = (1 − p^{τ_j}) P(past = τ)`, which is the conditional statement on
pasts of positive probability and says nothing on null pasts. `M(1) = 1` holds almost surely. -/
structure IsMorrisChain (p : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℕ) : Prop where
  /-- every `M j` is a random variable -/
  measurable : ∀ j, Measurable (M j)
  /-- `M(1) = 1` -/
  init : ∀ᵐ ω ∂P, M 1 ω = 1
  /-- the chain rises by one with probability `p^{M(j)}` given the past, and otherwise stays -/
  step : ∀ j : ℕ, 1 ≤ j → ∀ τ : ℕ → ℕ,
    P {ω | (∀ i, 1 ≤ i → i ≤ j → M i ω = τ i) ∧ M (j + 1) ω = τ j + 1} =
        ENNReal.ofReal (p ^ τ j) * P {ω | ∀ i, 1 ≤ i → i ≤ j → M i ω = τ i} ∧
      P {ω | (∀ i, 1 ≤ i → i ≤ j → M i ω = τ i) ∧ M (j + 1) ω = τ j} =
        ENNReal.ofReal (1 - p ^ τ j) * P {ω | ∀ i, 1 ≤ i → i ≤ j → M i ω = τ i}

end SkipListConc.Supplement


