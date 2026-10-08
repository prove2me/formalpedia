-- Prove2me | Definitions.Def_L0BnB_Strength_Relaxations
-- name    : L0BnB_Strength_Relaxations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:20.32639+00:00
-- url     : https://prove2.me/theorems/a2220e23-1dc4-400b-a65d-a8c438dc25ff
-- title:
--   The Big-M relaxation value $V_{B(M)}$ (2), the function $H$ of (37), and $G$ and $V_{PR(\infty)}$ of (6)
-- statement:
--   Fix a design matrix $X \in \mathbb R^{n\times p}$, a response $y \in \mathbb R^n$, parameters $\lambda_0,\lambda_2 > 0$ and a bound $M > 0$; write $[p] = \{1,\dots,p\}$ and $\psi_1(b;\lambda_0,\lambda_2)=2\lambda_0\,\mathcal B(b\sqrt{\lambda_2/\lambda_0})$ for the reverse Huber penalty of Theorem 1.
--
--   1. The **Big-M formulation** $B(M)$ (2) minimizes the objective $\tfrac12\|y-X\beta\|_2^2 + \lambda_0\sum_{i} z_i + \lambda_2\|\beta\|_2^2$ subject to $-Mz_i \le \beta_i \le Mz_i$ and $z_i \in \{0,1\}$, $i\in[p]$. Its **interval relaxation** replaces $z_i\in\{0,1\}$ by $z_i \in [0,1]$, and $V_{B(M)}$ is the optimal value of that relaxation:
--   $$V_{B(M)} = \inf\Big\{\tfrac12\|y-X\beta\|_2^2 + \lambda_0\sum_{i} z_i + \lambda_2\|\beta\|_2^2 \;:\; -Mz_i \le \beta_i \le Mz_i,\ 0\le z_i\le 1,\ i\in[p]\Big\}.$$
--   2. $H(\beta) = \tfrac12\|y-X\beta\|_2^2 + \sum_{i}\big(\tfrac{\lambda_0}{M}|\beta_i| + \lambda_2\beta_i^2\big)$, the function of (37).
--   3. $G(\beta) = \tfrac12\|y-X\beta\|_2^2 + \sum_{i}\psi_1(\beta_i;\lambda_0,\lambda_2)$, and, as displayed in (6),
--   $$V_{PR(\infty)} = \inf_{\beta\in\mathbb R^p} G(\beta).$$
--
--   Together with $V_{PR(M)}$ of the reduced problem (5), these are the relaxation values that Propositions 1 and 2 compare.
--
--   **Formalization Note** Norms are explicit sums over `Fin n` and `Fin p`. Optimal values are `sInf` of a set of reals; both sets are nonempty ($\beta = 0$, $z = 0$ is feasible) and bounded below by $0$ when $\lambda_0,\lambda_2 > 0$, so `sInf` is the true infimum. The paper writes $V_{PR(\infty)}$ via (6), crediting its reference [21] for the identification of (6) with the interval relaxation of $\mathrm{PR}(\infty)$ in $(\beta,z,s)$ variables; that identification is not part of this development, and $V_{PR(\infty)}$ is (6) as printed. $V_{B(M)}$ is defined over pairs $(\beta,z)$, not through $H$; the identity $V_{B(M)} = \min H$ is the separate statement (37). The least squares loss and $\psi_1$ are those of `L0BnB.Reduced`; $V_{PR(M)}$ is `L0BnB.Reduced.VPR`.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 5, (2); p. 6, (6); p. 7, Proposition 1 (V_B(M)); p. 28, (37) (H)

import Mathlib
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Reduced_Setup

open Matrix

namespace L0BnB.Strength

variable {n p : ℕ}

/-- The objective of the Big-M formulation (2), p. 5:
`½‖y − Xβ‖₂² + λ₀ Σᵢ zᵢ + λ₂ ‖β‖₂²`. -/
noncomputable def bigMObj (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ)
    (β z : Fin p → ℝ) : ℝ :=
  L0BnB.Reduced.lsLoss X y β + lam0 * ∑ i, z i + lam2 * ∑ i, β i ^ 2

/-- Feasibility in the interval relaxation of B(M): `−M zᵢ ≤ βᵢ ≤ M zᵢ` and `zᵢ ∈ [0, 1]`
(the binary `zᵢ ∈ {0, 1}` of (2) relaxed to the interval). -/
def bigMIntervalFeasible (M : ℝ) (β z : Fin p → ℝ) : Prop :=
  ∀ i, -M * z i ≤ β i ∧ β i ≤ M * z i ∧ 0 ≤ z i ∧ z i ≤ 1

/-- `V_{B(M)}`, the optimal objective of the interval relaxation of B(M) (Proposition 1, p. 7):
the infimum of the Big-M objective over all `(β, z)` feasible for the relaxation. For
`λ₀, λ₂ > 0` the set is nonempty (`β = z = 0`) and bounded below by `0`. -/
noncomputable def VB (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ) : ℝ :=
  sInf {v | ∃ β z : Fin p → ℝ, bigMIntervalFeasible M β z ∧ bigMObj X y lam0 lam2 β z = v}

/-- `H(β) = ½‖y − Xβ‖₂² + Σᵢ (λ₀/M |βᵢ| + λ₂ βᵢ²)`, the function in (37), p. 28. -/
noncomputable def H (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  L0BnB.Reduced.lsLoss X y β + ∑ i, (lam0 / M * |β i| + lam2 * β i ^ 2)

/-- `G(β) = ½‖y − Xβ‖₂² + Σᵢ ψ₁(βᵢ; λ₀, λ₂)`, the function in (6), p. 6. -/
noncomputable def G (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  L0BnB.Reduced.lsLoss X y β + ∑ i, L0BnB.Reduced.psi1 lam0 lam2 (β i)

/-- `V_{PR(∞)} = min_{β ∈ ℝᵖ} G(β)`, as displayed in (6), p. 6 (the paper credits the identification
of this value with the interval relaxation of PR(∞) to its reference [21]). For `λ₀, λ₂ > 0`, `G ≥ 0`,
so the infimum is finite. -/
noncomputable def VPRinf (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ) : ℝ :=
  sInf (G X y lam0 lam2 '' Set.univ)

end L0BnB.Strength


