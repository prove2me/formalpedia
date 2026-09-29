-- Prove2me | Definitions.Def_DRLogReg_RiskEstimation_Core
-- name    : DRLogReg_RiskEstimation_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:37:29.073664+00:00
-- url     : https://prove2.me/theorems/268132c1-2bde-46b8-a1fd-44ae3d00f7fd
-- title:
--   Definitions 1–2 — feature-label metric, Wasserstein distance and ball, empirical distribution
-- statement:
--   Let $V$ be a real vector space (the feature space $\mathbb R^n$) with an arbitrary norm $\|\cdot\|$, and let labels take values $y \in \{-1,+1\}$. The **feature-label space** is $\Xi = V \times \{-1,+1\}$, with generic element $\xi = (x,y)$.
--
--   1. **Metric (Definition 2).** For a weight $\kappa > 0$,
--   $$d\big((x,y),(x',y')\big) = \|x - x'\| + \kappa\,\frac{|y - y'|}{2}.$$
--   2. **Wasserstein distance (Definition 1).** For distributions $\mathbb Q, \mathbb P$ on $\Xi$,
--   $$W(\mathbb Q,\mathbb P) = \inf_{\Pi}\int_{\Xi^2} d(\xi,\xi')\,\Pi(d\xi,d\xi'),$$
--   the infimum over probability distributions $\Pi$ on $\Xi\times\Xi$ whose first marginal is $\mathbb Q$ and whose second marginal is $\mathbb P$; the value lies in $[0,\infty]$.
--   3. **Wasserstein ball.** $\mathbb B_\varepsilon(\mathbb P) = \{\mathbb Q \text{ a probability distribution on } \Xi : W(\mathbb Q,\mathbb P) \le \varepsilon\}$.
--   4. **Empirical distribution** of training samples $(\hat x_i,\hat y_i)$, $i = 1,\dots,N$:
--   $$\hat{\mathbb P}_N = \frac1N\sum_{i=1}^N \delta_{(\hat x_i,\hat y_i)}.$$
--
--   These are the ambiguity sets of distributionally robust logistic regression: every worst- and best-case quantity of the paper is an extremum over $\mathbb B_\varepsilon(\hat{\mathbb P}_N)$.
--
--   **Formalization Note.** The feature space is an abstract real normed space `V` standing for $(\mathbb R^n, \|\cdot\|)$. Labels are `Bool` with `sgn true = 1`, `sgn false = -1`. The metric is written literally, without simplifying $|y-y'|/2$ to an indicator. The Wasserstein distance and the radius are compared in $[0,\infty]$ (`ℝ≥0∞`), so no integrability side condition arises. Samples are indexed by `Fin N`.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 3, Definition 1 and the ball B_ε(P̂_N); p. 4, Definition 2

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-!
Objects of Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally Robust Logistic
Regression*, Advances in Neural Information Processing Systems 28 (NIPS 2015), pp. 1–4.

The feature space `(ℝⁿ, ‖·‖)` with an arbitrary norm is a real normed space `V`; the label set
`{−1, +1}` is `Bool` with `sgn true = +1`, `sgn false = −1`; the feature-label space is
`Ξ = V × Bool` with the product σ-algebra. A weight vector `β` is a continuous linear functional
`β : V →L[ℝ] ℝ`, `⟨β, x⟩` is `β x`, and the dual norm `‖β‖_*` is the operator norm `‖β‖`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The label `y ∈ {−1, +1}` as a real number: `true ↦ +1`, `false ↦ −1`
(Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015, p. 1). -/
def sgn (y : Bool) : ℝ := if y then 1 else -1

/-- Definition 2 (p. 4), the metric on the feature-label space `Ξ = ℝⁿ × {−1, +1}`:
`d((x, y), (x', y')) = ‖x − x'‖ + κ |y − y'| / 2`, for any norm `‖·‖` and a weight `κ > 0`. -/
noncomputable def featureLabelDist (κ : ℝ) (ξ ξ' : V × Bool) : ℝ :=
  ‖ξ.1 - ξ'.1‖ + κ * |sgn ξ.2 - sgn ξ'.2| / 2

variable [MeasurableSpace V]

/-- Definition 1 (p. 3), the (type-1) Wasserstein distance `W(Q, P)` with respect to the metric
`featureLabelDist κ` of Definition 2: the infimum of `∫ d(ξ, ξ') Π(dξ, dξ')` over probability
measures `Π` on `Ξ × Ξ` whose first marginal is `Q` and whose second marginal is `P`.
Valued in `[0, ∞]`. -/
noncomputable def wasserstein (κ : ℝ) (Q P : Measure (V × Bool)) : ℝ≥0∞ :=
  ⨅ (π : Measure ((V × Bool) × (V × Bool))) (_ : IsProbabilityMeasure π)
    (_ : π.map Prod.fst = Q) (_ : π.map Prod.snd = P),
    ∫⁻ p, ENNReal.ofReal (featureLabelDist κ p.1 p.2) ∂π

/-- The Wasserstein ball `B_ε(P) := {Q : W(Q, P) ≤ ε}` (p. 3): the probability measures on `Ξ`
within Wasserstein distance `ε` of `P`. -/
def wassersteinBall (κ ε : ℝ) (P : Measure (V × Bool)) : Set (Measure (V × Bool)) :=
  {Q | IsProbabilityMeasure Q ∧ wasserstein κ Q P ≤ ENNReal.ofReal ε}

/-- The empirical distribution `P̂_N = (1/N) ∑_{i=1}^N δ_{(x̂_i, ŷ_i)}` of the training samples
(p. 3); samples are indexed by `Fin N`. -/
noncomputable def empirical {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Measure (V × Bool) :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xhat i, yhat i)

end DRLogReg.RiskEstimation


