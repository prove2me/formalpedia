-- Prove2me | Definitions.Def_L0BnB_BigMvsPR_Relaxations
-- name    : L0BnB_BigMvsPR_Relaxations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:07.068889+00:00
-- url     : https://prove2.me/theorems/2ed818dc-65e6-4dd9-912e-4fb2df2f3689
-- title:
--   The relaxation values $V_{B(M)}$ (2), $V_{PR(\infty)}$ (6), the functions $H$, $G$, the sets $\mathcal S(\lambda_2)$, $\mathcal L(M)$ (9) and $v^*(M)$
-- statement:
--   Fix a design matrix $X \in \mathbb R^{n\times p}$, a response $y \in \mathbb R^n$ and parameters $\lambda_0, \lambda_2, M > 0$; write $[p] = \{1,\dots,p\}$ and $\|\beta\|_\infty \le M$ for $|\beta_i| \le M$ for all $i \in [p]$.
--
--   1. The **Big-M formulation** (2) minimizes $\tfrac12\|y - X\beta\|_2^2 + \lambda_0\sum_{i\in[p]} z_i + \lambda_2\|\beta\|_2^2$ subject to $-Mz_i \le \beta_i \le Mz_i$ and $z_i \in \{0,1\}$. Its **interval relaxation** replaces $z_i \in \{0,1\}$ by $z_i \in [0,1]$, and $V_{B(M)}$ denotes its optimal value:
--   $$V_{B(M)} = \inf\Big\{\tfrac12\|y - X\beta\|_2^2 + \lambda_0\sum_{i} z_i + \lambda_2\|\beta\|_2^2 \;:\; -Mz_i \le \beta_i \le Mz_i,\ 0 \le z_i \le 1\ \ \forall i\Big\}.$$
--   2. The function of (37) is $H(\beta) = \tfrac12\|y - X\beta\|_2^2 + \sum_{i\in[p]}\big(\tfrac{\lambda_0}{M}|\beta_i| + \lambda_2\beta_i^2\big)$.
--   3. The function of (6) is $G(\beta) = \tfrac12\|y - X\beta\|_2^2 + \sum_{i\in[p]}\psi_1(\beta_i;\lambda_0,\lambda_2)$, and
--   $$V_{PR(\infty)} = \inf_{\beta\in\mathbb R^p} G(\beta).$$
--   4. $\mathcal S(\lambda_2)$ is the set of minimizers of $G$ over $\mathbb R^p$ (with $X$, $y$, $\lambda_0$ fixed and $\lambda_2$ as a parameter), and
--   $$\mathcal L(M) = \{\lambda_2 > 0 \;:\; \exists \beta \in \mathcal S(\lambda_2) \text{ with } \|\beta\|_\infty \le M\}.$$
--   5. $v^*(M) = \inf_{\|\beta\|_\infty \le M} G(\beta)$.
--
--   These are the objects compared in Proposition 2: the lower bounds that the Big-M relaxation and the perspective relaxation $\mathrm{PR}(\infty)$ provide in a branch-and-bound method for $\ell_0\ell_2$-regularized least squares.
--
--   **Formalization Note** Norms are explicit sums; $X\beta$ is `X *ᵥ β`. Optimal values are real infima (`sInf`); the sets involved are nonempty ($\beta = z = 0$ is feasible) and bounded below by $0$ for $\lambda_0, \lambda_2 > 0$, so the infima are the intended values. The paper states that $V_{PR(\infty)}$, as displayed in (6), is the optimal value of the interval relaxation of $\mathrm{PR}(\infty)$ (a result it credits to its reference [21]); here $V_{PR(\infty)}$ is defined as the displayed minimum of $G$, and $\mathcal S(\lambda_2)$ as the set of minimizers of $G$, as the paper uses them in the proof of Proposition 2.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 5, (2); p. 6, (6); p. 7, (9) and Proposition 1 (V_B(M)); p. 28, (37) (H); p. 29, Proof of (11) (v*(M))

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_Reduced_Setup
import Definitions.Def_L0BnB_Strength_Relaxations

open Matrix

namespace L0BnB.BigMvsPR

variable {n p : ℕ}

/-- `S(λ₂)`, the set of optimal solutions (in `β`) of the interval relaxation of PR(∞), taken,
as the paper does in the proof of Proposition 2 (p. 30), as the set of minimizers of `G` in (6). -/
def S (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ) : Set (Fin p → ℝ) :=
  {β | ∀ β' : Fin p → ℝ, L0BnB.Strength.G X y lam0 lam2 β ≤ L0BnB.Strength.G X y lam0 lam2 β'}

/-- `L(M) := {λ₂ > 0 | ∃ β ∈ S(λ₂) s.t. ‖β‖_∞ ≤ M}`, (9), p. 7. Here `λ₂` is the variable;
`X`, `y`, `λ₀` are fixed. -/
def L (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 M : ℝ) : Set ℝ :=
  {l | 0 < l ∧ ∃ β ∈ S X y lam0 l, ∀ i, |β i| ≤ M}

/-- `v*(M) = min_{‖β‖_∞ ≤ M} L0BnB.Strength.G(β)`, defined in the proof of (11), p. 29. -/
noncomputable def vStar (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ) : ℝ :=
  sInf (L0BnB.Strength.G X y lam0 lam2 '' L0BnB.Reduced.box p M)

end L0BnB.BigMvsPR


