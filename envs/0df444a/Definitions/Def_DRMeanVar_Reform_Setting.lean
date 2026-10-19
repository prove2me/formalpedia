-- Prove2me | Definitions.Def_DRMeanVar_Reform_Setting
-- name    : DRMeanVar_Reform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:27.383768+00:00
-- url     : https://prove2.me/theorems/edea15e6-9fb9-41a9-ba2a-2cb140cc4978
-- title:
--   §1–§2.2 — Wasserstein portfolio model, empirical and population moments, and the objectives of (2) and (9)
-- statement:
--   Let $R_1,\ldots,R_n\in\mathbb R^d$ be observed return vectors, with $n\ge1$. The **empirical law** is $P_n=n^{-1}\sum_i\delta_{R_i}$. For $1\le q<\infty$, use transportation cost $c(u,w)=\|w-u\|_q^2$ and let $D_c(P,P_n)$ be the least expected cost among couplings with first marginal $P$ and second marginal $P_n$. For $\delta\ge0$, the **ambiguity set** is
--   $$U_\delta(P_n)=\{P\text{ a probability law}:D_c(P,P_n)\le\delta\}. $$
--
--   A portfolio $\varphi\in\mathbb R^d$ is feasible for target $\bar\alpha$ when its weights sum to one and its expected return is at least $\bar\alpha$ under every law in the ambiguity set. The module defines the expected return, second moment and variance of $\varphi^TR$ under $P$, and their empirical versions with normalization $1/n$. It also defines the worst-case variance in (2), the squared norm-penalized empirical standard deviation in (9), and $h(\alpha,\varphi)$ from Proposition 3.
--
--   These definitions supply a common model for all statements in the mission.
--
--   **Formalization Note** Returns are functions on `Fin d`. The worst-case objective is an extended-real supremum. The portfolio moments use real Bochner integrals; finite second moments for laws in the quadratic-cost ball are a proof obligation, rather than an added restriction on the ball. The finite empirical variance uses $1/n$. The feasible mean constraint is stated pointwise for all laws in the ball, equivalent to the paper's minimum bound.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, pp. 2–5, (2)–(4), (7), (9), Proposition 3

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost

open MeasureTheory
open scoped BigOperators

namespace DRMeanVar.Reform

/-- The squared `ℓ_q` transportation cost of (4). -/
noncomputable def lqSqCost {d : ℕ} (q : ENNReal) (u w : Fin d → ℝ) : ENNReal :=
  ENNReal.ofReal (‖WithLp.toLp q (w - u)‖ ^ 2)

/-- The empirical distribution of the return sample. -/
noncomputable def Pn {d n : ℕ} (R : Fin n → (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (R i)

/-- The Wasserstein ambiguity set around the empirical distribution. -/
noncomputable def U {d n : ℕ} (q : ENNReal) (δ : ℝ)
    (R : Fin n → (Fin d → ℝ)) : Set (Measure (Fin d → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    RWPI.SqrtLasso.transportCost (lqSqCost q) P (Pn R) ≤ ENNReal.ofReal δ}

/-- The expected portfolio return under a probability law. -/
noncomputable def pMean {d : ℕ} (P : Measure (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  ∫ x, φ ⬝ᵥ x ∂P

/-- The expected square of the portfolio return. -/
noncomputable def pSecond {d : ℕ} (P : Measure (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  ∫ x, (φ ⬝ᵥ x) ^ 2 ∂P

/-- The variance of the portfolio return under a probability law. -/
noncomputable def pVar {d : ℕ} (P : Measure (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  pSecond P φ - (pMean P φ) ^ 2

/-- The empirical mean of portfolio returns, normalized by `1/n`. -/
noncomputable def empMean {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, φ ⬝ᵥ R i

/-- The empirical second moment of portfolio returns, normalized by `1/n`. -/
noncomputable def empSecond {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (φ ⬝ᵥ R i) ^ 2

/-- The empirical variance of portfolio returns, normalized by `1/n`. -/
noncomputable def empVar {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, (φ ⬝ᵥ R i - empMean R φ) ^ 2

/-- The budget and robust mean constraints defining the feasible portfolios. -/
noncomputable def F {d n : ℕ} (q : ENNReal) (δ αbar : ℝ)
    (R : Fin n → (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {φ | (∑ i, φ i) = 1 ∧ ∀ P ∈ U q δ R, αbar ≤ pMean P φ}

/-- The worst-case variance objective of (2), with an extended-real supremum. -/
noncomputable def robustObj {d n : ℕ} (q : ENNReal) (δ : ℝ)
    (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) : EReal :=
  ⨆ P ∈ U q δ R, (pVar P φ : EReal)

/-- The empirical variance objective with norm penalty in (9). -/
noncomputable def dualObj {d n : ℕ} (p : ENNReal) (δ : ℝ)
    (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) : ℝ :=
  (Real.sqrt (empVar R φ) + Real.sqrt δ * ‖WithLp.toLp p φ‖) ^ 2

/-- The formula `h(α, φ)` of Proposition 3. -/
noncomputable def hFun {d n : ℕ} (p : ENNReal) (δ : ℝ)
    (R : Fin n → (Fin d → ℝ)) (α : ℝ) (φ : Fin d → ℝ) : ℝ :=
  empSecond R φ + 2 * (α - empMean R φ) * empMean R φ +
    δ * ‖WithLp.toLp p φ‖ ^ 2 +
    2 * Real.sqrt (δ * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2) *
      Real.sqrt (empVar R φ)

end DRMeanVar.Reform


