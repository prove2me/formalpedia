-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_IsUniformlyApproachable
-- name    : OnlineConvexOpt_Approachability_IsUniformlyApproachable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:39.942922+00:00
-- url     : https://prove2.me/theorems/3ee0e7a4-30da-444d-9df9-33163d8fe1c3
-- title:
--   Uniformly approachable set (Definition 13.3, uniform reading)
-- statement:
--   With the data of Definition 13.3, the set $S$ is **uniformly approachable** if there is an admissible algorithm $\mathcal A$ such that the worst case over all column sequences of the distance tends to zero: for every $\varepsilon>0$ there is $T_0$ such that
--
--   $$
--   \mathrm{Dist}\Bigl(\frac1T\sum_{t=0}^{T-1}u(x_t,y_t),\,S\Bigr)\le\varepsilon\qquad\text{for all } T\ge T_0 \text{ and all } y_0,y_1,\dots\in\mathcal K_2 ,
--   $$
--
--   with $x_t=\mathcal A_t(y_0,\dots,y_{t-1})$.
--
--   Uniform approachability implies approachability in the per-sequence sense. Definition 13.3's "for any sequence $y_1,\dots,y_T\in\mathcal K_2$" admits both readings; Blackwell's theorem holds for both.
--
--   **Formalization Note** Quantifier order: algorithm, then $\varepsilon$, then $T_0$, then $T\ge T_0$ and the sequence. The distance is `Metric.infDist`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Definition 13.3, p. 209 (PDF p. 231)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachabilityAlg
import Definitions.Def_OnlineConvexOpt_Approachability_avgPayoff

namespace OnlineConvexOpt.Approachability

/-- **Uniformly approachable set** (Definition 13.3, uniform reading).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
Definition 13.3, p. 209: "… we say that a set S ⊆ ℝ^d is approachable if there exists some
algorithm A … which iteratively selects points K1 ∋ x_t ← A(y1, y2, . . . , y_{t−1}), such that,
for any sequence y1, y2, . . . , yT ∈ K2, we have Dist((1/T) Σ_{t=1}^T u(x_t, y_t), S) → 0 as
T → ∞."

`IsUniformlyApproachable K₁ K₂ u S`: there is an algorithm `A` playing in `K₁` on `K₂`-histories
such that the worst case, over all sequences `y : ℕ → K₂`, of the distance from the average
payoff after `T` rounds to `S` tends to `0`: for every `ε > 0` there is `T₀` with distance `≤ ε`
for all `T ≥ T₀` and all sequences.

**Formalization Note.** Reading R1-U: the uniform reading of "for any sequence y1, …, yT ∈ K2"
(the horizon-`T` sequence is arbitrary, so the convergence is uniform over sequences). It implies
`IsApproachable` (R1-P). Quantifier order `∃ A, ∀ ε, ∃ T₀, ∀ T ≥ T₀, ∀ y`. `Dist` is
`Metric.infDist`, as in `IsApproachable`. -/
def IsUniformlyApproachable {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ A : (t : ℕ) → (Fin t → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n),
    IsApproachabilityAlg K₁ K₂ A ∧
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
        ∀ y : ℕ → EuclideanSpace ℝ (Fin m), (∀ t, y t ∈ K₂) →
          Metric.infDist (avgPayoff u A y T) S ≤ ε

end OnlineConvexOpt.Approachability


