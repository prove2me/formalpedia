-- Prove2me | Definitions.Def_DRLogReg_RiskEstimation_Program
-- name    : DRLogReg_RiskEstimation_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:38:37.546046+00:00
-- url     : https://prove2.me/theorems/8e8fb98c-bac3-430d-b5ea-5c5436dbceeb
-- title:
--   Theorem 3, Eqs. (10a)–(10b) — the linear programs for the worst- and best-case risks
-- statement:
--   Fix $\kappa > 0$, $\varepsilon \ge 0$, training samples $(\hat x_i,\hat y_i)_{i=1}^N$ and a weight vector $\hat\beta$ with dual norm $\|\hat\beta\|_*$. The decision variables are a scalar $\lambda$ and vectors $s, r, t \in \mathbb R^N$.
--
--   1. **Objective** (shared): $\lambda\varepsilon + \frac1N\sum_{i=1}^N s_i$.
--   2. **Feasible set of (10a)**: for all $i \le N$,
--   $$1 - r_i\hat y_i\langle\hat\beta,\hat x_i\rangle \le s_i,\quad 1 + t_i\hat y_i\langle\hat\beta,\hat x_i\rangle - \lambda\kappa \le s_i,\quad r_i\|\hat\beta\|_* \le \lambda,\quad t_i\|\hat\beta\|_* \le \lambda,\quad r_i,t_i,s_i \ge 0.$$
--   3. **Feasible set of (10b)**: for all $i \le N$,
--   $$1 + r_i\hat y_i\langle\hat\beta,\hat x_i\rangle \le s_i,\quad 1 - t_i\hat y_i\langle\hat\beta,\hat x_i\rangle - \lambda\kappa \le s_i,\quad r_i\|\hat\beta\|_* \le \lambda,\quad t_i\|\hat\beta\|_* \le \lambda,\quad r_i,t_i,s_i \ge 0.$$
--
--   For fixed data both are linear programs in $(\lambda, s, r, t)$; Theorem 3 identifies their optimal values with the worst- and best-case misclassification risks.
--
--   **Formalization Note.** A decision is a tuple `(λ, s, r, t) : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)`. $\|\hat\beta\|_*$ is the operator norm of `βhat : V →L[ℝ] ℝ`, which is the dual norm of the norm on `V`. No sign constraint on $\lambda$ is added: $\lambda \ge 0$ is implied by $r_i\|\hat\beta\|_* \le \lambda$ with $r_i \ge 0$ (when $N \ge 1$).
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 5, Theorem 3, Eqs. (10a) and (10b)

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core

namespace DRLogReg.RiskEstimation

/-!
The linear programs (10a) and (10b) of Theorem 3 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn,
*Distributionally Robust Logistic Regression*, NIPS 2015, p. 5). A decision is a tuple
`(λ, s, r, t) : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)`; `β̂` is data, and `‖β̂‖` is the
operator norm, i.e. the dual norm `‖β̂‖_*` of the norm of `V`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The feasible set of the linear program (10a) (p. 5): for all `i ≤ N`,
`1 − r_i ŷ_i⟨β̂, x̂_i⟩ ≤ s_i`, `1 + t_i ŷ_i⟨β̂, x̂_i⟩ − λκ ≤ s_i`, `r_i‖β̂‖_* ≤ λ`,
`t_i‖β̂‖_* ≤ λ`, and `r_i, t_i, s_i ≥ 0`. -/
def feasible10a (κ : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool) (βhat : V →L[ℝ] ℝ) :
    Set (ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) :=
  {p | ∀ i,
    1 - p.2.2.1 i * sgn (yhat i) * βhat (xhat i) ≤ p.2.1 i ∧
    1 + p.2.2.2 i * sgn (yhat i) * βhat (xhat i) - p.1 * κ ≤ p.2.1 i ∧
    p.2.2.1 i * ‖βhat‖ ≤ p.1 ∧ p.2.2.2 i * ‖βhat‖ ≤ p.1 ∧
    0 ≤ p.2.2.1 i ∧ 0 ≤ p.2.2.2 i ∧ 0 ≤ p.2.1 i}

/-- The feasible set of the linear program (10b) (p. 5): for all `i ≤ N`,
`1 + r_i ŷ_i⟨β̂, x̂_i⟩ ≤ s_i`, `1 − t_i ŷ_i⟨β̂, x̂_i⟩ − λκ ≤ s_i`, `r_i‖β̂‖_* ≤ λ`,
`t_i‖β̂‖_* ≤ λ`, and `r_i, t_i, s_i ≥ 0`. -/
def feasible10b (κ : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool) (βhat : V →L[ℝ] ℝ) :
    Set (ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) :=
  {p | ∀ i,
    1 + p.2.2.1 i * sgn (yhat i) * βhat (xhat i) ≤ p.2.1 i ∧
    1 - p.2.2.2 i * sgn (yhat i) * βhat (xhat i) - p.1 * κ ≤ p.2.1 i ∧
    p.2.2.1 i * ‖βhat‖ ≤ p.1 ∧ p.2.2.2 i * ‖βhat‖ ≤ p.1 ∧
    0 ≤ p.2.2.1 i ∧ 0 ≤ p.2.2.2 i ∧ 0 ≤ p.2.1 i}

/-- The common objective of (10a) and (10b) (p. 5): `λε + (1/N) ∑_{i=1}^N s_i`. -/
noncomputable def objective10 (ε : ℝ) {N : ℕ}
    (p : ℝ × (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  p.1 * ε + (N : ℝ)⁻¹ * ∑ i, p.2.1 i

end DRLogReg.RiskEstimation


