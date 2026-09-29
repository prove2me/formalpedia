-- Prove2me | Definitions.Def_DRLogReg_Reformulation_Program
-- name    : DRLogReg_Reformulation_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:33:21.528382+00:00
-- url     : https://prove2.me/theorems/0161df15-1417-4ae8-a6d0-d86ab10016ed
-- title:
--   Theorem 1, eq. (7) — the convex program: feasible set, objective, optimal value
-- statement:
--   Fix $\kappa$, training samples $(\hat x_i,\hat y_i)_{i=1}^N$ in $V\times\{-1,+1\}$, and a radius $\varepsilon$. Program (7) has decision variables $\beta$ (a linear functional on $V$), $\lambda\in\mathbb R$ and $s\in\mathbb R^N$:
--   $$\begin{aligned}\min_{\beta,\lambda,s}\quad & \lambda\varepsilon + \frac1N\sum_{i=1}^N s_i\\ \text{s.t.}\quad & l_\beta(\hat x_i,\hat y_i) \le s_i && \forall i\le N,\\ & l_\beta(\hat x_i,-\hat y_i) - \lambda\kappa \le s_i && \forall i\le N,\\ & \|\beta\|_* \le \lambda.\end{aligned}$$
--
--   1. The **feasible set** is the set of triples $(\beta,\lambda,s)$ satisfying the three constraint groups.
--   2. The **objective** is $\lambda\varepsilon + \frac1N\sum_i s_i$.
--   3. The **optimal value** is the infimum of the objective over the feasible set, taken in $[0,\infty]$.
--
--   Theorem 1 identifies this optimal value with the optimal value of the distributionally robust logistic regression problem (6).
--
--   **Formalization Note.** For $\varepsilon \ge 0$ the objective is nonnegative on the feasible set ($\lambda \ge \|\beta\|_* \ge 0$ and $s_i \ge l_\beta(\hat x_i,\hat y_i) > 0$), so taking the infimum of its nonnegative part in `ℝ≥0∞` gives the true optimal value. The dual norm is the operator norm of `β : V →L[ℝ] ℝ`; the label $-\hat y_i$ is `!ŷ i`.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Theorem 1, eq. (7)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core

open scoped ENNReal

namespace DRLogReg.Reformulation

/-!
The convex program (7) of Theorem 1 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn,
*Distributionally Robust Logistic Regression*, NIPS 2015, p. 4). A decision is a triple
`(β, λ, s) : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)`; `‖β‖` is the operator norm, i.e. the dual norm
`‖β‖_*` of the norm of `V`.
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The feasible set of program (7) (p. 4):
`l_β(x̂_i, ŷ_i) ≤ s_i` and `l_β(x̂_i, −ŷ_i) − λκ ≤ s_i` for all `i ≤ N`, and `‖β‖_* ≤ λ`. -/
def feasible7 (κ : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool) :
    Set ((V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)) :=
  {p | (∀ i, logloss p.1 (xhat i) (yhat i) ≤ p.2.2 i) ∧
       (∀ i, logloss p.1 (xhat i) (!yhat i) - p.2.1 * κ ≤ p.2.2 i) ∧
       ‖p.1‖ ≤ p.2.1}

/-- The objective of program (7) (p. 4): `λε + (1/N) ∑_{i=1}^N s_i`. -/
noncomputable def objective7 (ε : ℝ) {N : ℕ} (p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)) : ℝ :=
  p.2.1 * ε + (N : ℝ)⁻¹ * ∑ i, p.2.2 i

/-- The optimal value of program (7), as an element of `[0, ∞]`: the infimum of the objective
over the feasible set. For `ε ≥ 0` the objective is nonnegative on the feasible set (`λ ≥ ‖β‖ ≥ 0`
and `s_i ≥ l_β(x̂_i, ŷ_i) > 0`), so `ENNReal.ofReal` loses nothing. -/
noncomputable def value7 (κ ε : ℝ) {N : ℕ} (xhat : Fin N → V) (yhat : Fin N → Bool) : ℝ≥0∞ :=
  ⨅ p ∈ feasible7 κ xhat yhat, ENNReal.ofReal (objective7 ε p)

end DRLogReg.Reformulation


