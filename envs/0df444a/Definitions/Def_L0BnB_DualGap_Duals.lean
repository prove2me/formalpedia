-- Prove2me | Definitions.Def_L0BnB_DualGap_Duals
-- name    : L0BnB_DualGap_Duals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:36.658423+00:00
-- url     : https://prove2.me/theorems/5923ae45-20fb-4128-a68b-f88916503437
-- title:
--   The duals (20)–(22), the dual variables (23)–(24) and the dual feasible solutions (25), (27)
-- statement:
--   In the setting of the reduced relaxation (5) (data $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M>0$), define for $\alpha\in\mathbb R^n$, a scalar $\gamma_i$ and a coordinate $i$
--   $$
--   v(\alpha,\gamma_i)=\Big[\frac{(\alpha^\top X_i-\gamma_i)^2}{4\lambda_2}-\lambda_0\Big]_+ + M|\gamma_i| \qquad (21)
--   $$
--   and the dual objectives
--   $$
--   h_1(\alpha,\gamma)=-\tfrac12\|\alpha\|_2^2-\alpha^\top y-\sum_{i\in[p]}v(\alpha,\gamma_i) \quad (20),\qquad h_2(\rho,\mu)=-\tfrac12\|\rho\|_2^2-\rho^\top y-M\|\mu\|_1 \quad (22),
--   $$
--   where (22) carries the constraints $|\rho^\top X_i|-\mu_i\le\lambda_0/M+\lambda_2M$ for all $i\in[p]$.
--
--   **Dual variables from a primal point** (23)–(24). For $\beta^*\in\mathbb R^p$ with $r^*=y-X\beta^*$:
--   $\alpha^*=\rho^*=-r^*$,
--   $$
--   \gamma^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(\alpha^{*\top}X_i-2M\lambda_2\operatorname{sign}(\alpha^{*\top}X_i)\big),\qquad \mu^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(|\rho^{*\top}X_i|-\lambda_0/M-\lambda_2M\big).
--   $$
--
--   **Dual feasible solutions from an inexact primal point** (25), (27). For $\hat\beta$ with $\hat r=y-X\hat\beta$: $\hat\alpha=\hat\rho=-\hat r$; $\hat\gamma$ is any maximizer of $h_1(\hat\alpha,\cdot)$ over $\mathbb R^p$, and $\hat\mu$ is any maximizer of $h_2(\hat\rho,\cdot)$ over the $\mu$ for which $(\hat\rho,\mu)$ satisfies the constraints of (22).
--
--   Finally, the constant of Lemma 2: $c_i=(2\lambda_2)^{-1}$ if $|\beta^*_i|<M$ and $c_i=M$ if $|\beta^*_i|=M$.
--
--   These are the objects compared by the dual-bound guarantee (Theorem 3): the dual values at $(\hat\alpha,\hat\gamma)$, $(\hat\rho,\hat\mu)$ are computable from an inexact primal solution, those at $(\alpha^*,\gamma^*)$, $(\rho^*,\mu^*)$ from an optimal one.
--
--   **Formalization Note** $(23)$–$(24)$ are definitions by formula; that they are optimal for the duals (Theorem 2 of the paper) is not built in and is not used. `sign` is `Real.sign` with $\operatorname{sign}(0)=0$. $[a]_+$ is `max a 0`. The maximizer conditions (25), (27) are predicates on $\hat\gamma$, $\hat\mu$, not choices. $c_i$ is written "$(2\lambda_2)^{-1}$ if $|\beta^*_i|<M$, else $M$", which is the paper's two cases for $\beta^*$ in the box.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, pp. 13–14, Theorem 2 (20)–(24), Dual Feasible Solutions (25), (27); p. 31, Lemma 2 (cᵢ)

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.DualGap

/-! Dual objects of Hazimeh, Mazumder, Saab, arXiv:2004.06152v2, §3.2 (pp. 13–14): the function `v`
(21), the dual objectives `h₁` (20) and `h₂` (22) with the constraint of (22), the dual variables
(23)–(24) built from a primal point `β*`, and the dual feasible solutions (25) and (27) built from an
inexact primal point `β̂`. The formulas (23)–(24) are taken as definitions; their optimality for the
duals is Theorem 2 of the paper and is not built in. -/

/-- `v(α, γᵢ) := [(αᵀXᵢ − γᵢ)²/(4λ₂) − λ₀]₊ + M|γᵢ|` (21), p. 13, for coordinate `i`. -/
noncomputable def v {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam0 lam2 M : ℝ)
    (α : Fin n → ℝ) (g : ℝ) (i : Fin p) : ℝ :=
  max ((colInner X α i - g) ^ 2 / (4 * lam2) - lam0) 0 + M * |g|

/-- `h₁(α, γ) := −½‖α‖₂² − αᵀy − ∑_{i ∈ [p]} v(α, γᵢ)` (20), p. 13. -/
noncomputable def h1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (α : Fin n → ℝ) (γ : Fin p → ℝ) : ℝ :=
  -(1 / 2) * ∑ r, α r ^ 2 - ∑ r, α r * y r - ∑ i, v X lam0 lam2 M α (γ i) i

/-- `α̂ = −r̂` with `r̂ = y − Xβ̂` (25), p. 14. -/
noncomputable def alphaHat {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (βhat : Fin p → ℝ) : Fin n → ℝ :=
  fun r => -resid X y βhat r

/-- `ρ̂ = −r̂` with `r̂ = y − Xβ̂` (27), p. 14. -/
noncomputable def rhoHat {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (βhat : Fin p → ℝ) : Fin n → ℝ :=
  fun r => -resid X y βhat r

/-- (25), p. 14: `γ̂ ∈ argmax_{γ ∈ ℝᵖ} h₁(α̂, γ)` with `α̂ = −r̂`. -/
def IsGammaHat {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βhat γhat : Fin p → ℝ) : Prop :=
  ∀ γ : Fin p → ℝ, h1 X y lam0 lam2 M (alphaHat X y βhat) γ ≤ h1 X y lam0 lam2 M (alphaHat X y βhat) γhat

/-- (27), p. 14: `µ̂ ∈ argmax_{µ ∈ ℝᵖ} h₂(ρ̂, µ)` subject to `(ρ̂, µ)` feasible for (22),
with `ρ̂ = −r̂`. -/
def IsMuHat {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βhat μhat : Fin p → ℝ) : Prop :=
  L0BnB.Duality.Feas22 X lam0 lam2 M (rhoHat X y βhat) μhat ∧
    ∀ μ : Fin p → ℝ, L0BnB.Duality.Feas22 X lam0 lam2 M (rhoHat X y βhat) μ →
      L0BnB.Duality.h2 y M (rhoHat X y βhat) μ ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat

/-- The constant `cᵢ` of Lemma 2 (p. 31): `cᵢ = (2λ₂)⁻¹` if `|β*ᵢ| < M` and `cᵢ = M` if
`|β*ᵢ| = M` (for `β*` in the box these are the only cases). -/
noncomputable def cLemma2 {p : ℕ} (lam2 M : ℝ) (βs : Fin p → ℝ) (i : Fin p) : ℝ :=
  if |βs i| < M then (2 * lam2)⁻¹ else M

end L0BnB.DualGap


