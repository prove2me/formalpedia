-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_IsApproachable
-- name    : OnlineConvexOpt_Approachability_IsApproachable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:14.247053+00:00
-- url     : https://prove2.me/theorems/3c15a344-f41b-4cc0-9cf1-96553b0927af
-- title:
--   Approachable set (Definition 13.3)
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$, $\mathcal K_2\subseteq\mathbb R^m$, a payoff $u$ and a set $S\subseteq\mathbb R^d$ be given. The set $S$ is **approachable** if there is an admissible algorithm $\mathcal A$ (playing in $\mathcal K_1$ whenever the past column plays lie in $\mathcal K_2$) such that for every sequence $y_0,y_1,\dots\in\mathcal K_2$
--
--   $$
--   \mathrm{Dist}\Bigl(\frac1T\sum_{t=0}^{T-1}u(x_t,y_t),\,S\Bigr)\to 0\qquad (T\to\infty),
--   $$
--
--   where $x_t=\mathcal A_t(y_0,\dots,y_{t-1})$ and $\mathrm{Dist}(w,S)=\inf_{s\in S}\|w-s\|$ is the Euclidean distance.
--
--   The algorithm is fixed before the sequence. Since it is deterministic, sequences chosen adaptively by the column player are covered.
--
--   **Formalization Note** This is the per-sequence reading of "for any sequence … $\to 0$". The uniform reading is `IsUniformlyApproachable`; the mission's goal characterizes both. The distance is `Metric.infDist`, which is $0$ for the empty set, so statements about approachability assume $S$ nonempty.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Definition 13.3, p. 209 (PDF p. 231)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachabilityAlg
import Definitions.Def_OnlineConvexOpt_Approachability_avgPayoff

namespace OnlineConvexOpt.Approachability

/-- **Approachable set** (Definition 13.3, per-sequence reading).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
Definition 13.3, p. 209: "Given a generalized vector game K1, K2, {u(·,·)}, we say that a set
S ⊆ ℝ^d is approachable if there exists some algorithm A, called an approachability algorithm,
which iteratively selects points K1 ∋ x_t ← A(y1, y2, . . . , y_{t−1}), such that, for any
sequence y1, y2, . . . , yT ∈ K2, we have Dist((1/T) Σ_{t=1}^T u(x_t, y_t), S) → 0 as T → ∞."

`IsApproachable K₁ K₂ u S`: there is an algorithm `A` playing in `K₁` on `K₂`-histories such that
for every sequence `y : ℕ → K₂` the Euclidean distance from the average payoff after `T` rounds
to `S` tends to `0` as `T → ∞`.

**Formalization Note.**
* Reading R1-P: "for any sequence … → 0" is read per sequence (for each sequence the distance
  tends to `0`). The uniform reading is `IsUniformlyApproachable`; the goal theorem states the
  characterization for both.
* The algorithm is chosen before the sequence (`∃ A, ∀ y`).
* `Dist(w, S) = min_{x∈S} ‖w − x‖` (p. 209) is `Metric.infDist w S`; it equals the printed
  minimum for nonempty closed `S`. `Metric.infDist w ∅ = 0`, so every statement about
  approachability assumes `S` nonempty.
* Adaptive opponents are covered: `A` is deterministic, so the plays of an adaptive opponent
  form one fixed sequence `y`. -/
def IsApproachable {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ A : (t : ℕ) → (Fin t → EuclideanSpace ℝ (Fin m)) → EuclideanSpace ℝ (Fin n),
    IsApproachabilityAlg K₁ K₂ A ∧
      ∀ y : ℕ → EuclideanSpace ℝ (Fin m), (∀ t, y t ∈ K₂) →
        Filter.Tendsto (fun T => Metric.infDist (avgPayoff u A y T) S) Filter.atTop (nhds 0)

end OnlineConvexOpt.Approachability


