-- Prove2me | Definitions.Def_DRLogReg_RiskEstimation_Risk
-- name    : DRLogReg_RiskEstimation_Risk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:38:08.692909+00:00
-- url     : https://prove2.me/theorems/4d0b193f-d567-4247-a587-dcf58f0b69a1
-- title:
--   §3.3 — logistic classifier, misclassification risk, worst- and best-case risks
-- statement:
--   Let $\beta$ be a weight vector, i.e. a continuous linear functional $x \mapsto \langle\beta,x\rangle$ on the feature space. Logistic regression models the conditional label probability as
--   $$\operatorname{Prob}(y \mid x) = \big[1 + \exp(-y\langle\beta,x\rangle)\big]^{-1}. \qquad (1)$$
--
--   1. **Classifier.** $f_\beta(x) = +1$ if $\operatorname{Prob}(+1\mid x) > 0.5$, and $f_\beta(x) = -1$ otherwise.
--   2. **Risk.** For a distribution $\mathbb P$ on $\Xi = \mathbb R^n \times\{-1,+1\}$, the misclassification probability
--   $$\mathfrak R(\beta) = \mathbb P\big[y \ne f_\beta(x)\big].$$
--   3. **Worst-case risk** over the Wasserstein ball of radius $\varepsilon$ around the empirical distribution $\hat{\mathbb P}_N$:
--   $$\mathfrak R_{\max}(\beta) = \sup_{\mathbb Q \in \mathbb B_\varepsilon(\hat{\mathbb P}_N)} \mathbb E^{\mathbb Q}\big[\mathbb 1_{\{y\langle\beta,x\rangle \le 0\}}\big].$$
--   4. **Best-case risk**:
--   $$\mathfrak R_{\min}(\beta) = \inf_{\mathbb Q \in \mathbb B_\varepsilon(\hat{\mathbb P}_N)} \mathbb E^{\mathbb Q}\big[\mathbb 1_{\{y\langle\beta,x\rangle < 0\}}\big].$$
--
--   Note the non-strict inequality in the worst case and the strict one in the best case. These are the quantities whose computation Theorem 3 reduces to linear programs.
--
--   **Formalization Note.** $\beta$ has type `V →L[ℝ] ℝ`. The risk and the worst/best-case risks are values of measures on sets, in $[0,\infty]$ (`ℝ≥0∞`); the supremum and infimum range exactly over the probability measures in the ball. The classifier is defined literally from (1); the paper's remark that $\mathfrak R(\beta) = \mathbb E^{\mathbb P}[\mathbb 1_{\{y\langle\beta,x\rangle\le 0\}}]$ is not used as a definition, because it fails on the hyperplane $\langle\beta,x\rangle = 0$.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 1, Eq. (1); p. 5, §3.3 and Theorem 3 (definitions of R_max, R_min)

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-!
The logistic classifier, its misclassification risk, and the worst- and best-case risks over the
Wasserstein ball of §3.3 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, *Distributionally
Robust Logistic Regression*, NIPS 2015, pp. 1 and 5). Probabilities and expectations of
indicators are values `Q S` of measures, in `[0, ∞]`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The logistic-regression model of the conditional label probability, eq. (1) (p. 1):
`Prob(y | x) = [1 + exp(−y⟨β, x⟩)]⁻¹`. -/
noncomputable def condProb (β : V →L[ℝ] ℝ) (y : Bool) (x : V) : ℝ :=
  (1 + Real.exp (-(sgn y * β x)))⁻¹

/-- The classifier of §3.3 (p. 5): `f_β(x) = +1` if `Prob(+1 | x) > 0.5`, and `−1` otherwise,
with `Prob(· | x)` from eq. (1). -/
noncomputable def classify (β : V →L[ℝ] ℝ) (x : V) : Bool :=
  decide (condProb β true x > 1 / 2)

variable [MeasurableSpace V]

/-- The risk `R(β) := P[y ≠ f_β(x)]` of §3.3 (p. 5): the probability, under the distribution `P`
on `Ξ = ℝⁿ × {−1, +1}`, that the label differs from the classifier's prediction. -/
noncomputable def risk (P : Measure (V × Bool)) (β : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  P {ξ | ξ.2 ≠ classify β ξ.1}

/-- The worst-case risk of Theorem 3(i) (p. 5):
`R_max(β) := sup_{Q ∈ B_ε(P̂_N)} E^Q[1{y⟨β, x⟩ ≤ 0}]`, in `[0, ∞]`. -/
noncomputable def riskMax (κ ε : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool)
    (β : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨆ Q ∈ wassersteinBall κ ε (empirical xhat yhat), Q {ξ | sgn ξ.2 * β ξ.1 ≤ 0}

/-- The best-case risk of Theorem 3(ii) (p. 5):
`R_min(β) := inf_{Q ∈ B_ε(P̂_N)} E^Q[1{y⟨β, x⟩ < 0}]`, in `[0, ∞]`. -/
noncomputable def riskMin (κ ε : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool)
    (β : V →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨅ Q ∈ wassersteinBall κ ε (empirical xhat yhat), Q {ξ | sgn ξ.2 * β ξ.1 < 0}

end DRLogReg.RiskEstimation


