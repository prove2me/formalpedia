-- Prove2me | Definitions.Def_L0BnB_Duality_Dual
-- name    : L0BnB_Duality_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:52.918268+00:00
-- url     : https://prove2.me/theorems/56207db1-6dcb-4123-bd80-daed4e38affa
-- title:
--   The duals (20)–(22) of the reduced relaxation, the dual variables (23)–(24) and the coordinate function $D_i$
-- statement:
--   Keep the data of problem (5): $X\in\mathbb R^{n\times p}$ with columns $X_1,\dots,X_p$, $y\in\mathbb R^n$, $\lambda_0,\lambda_2,M$. Write $[a]_+=\max\{a,0\}$.
--
--   **The dual (20)–(21).** For $\alpha\in\mathbb R^n$ and $\gamma\in\mathbb R^p$,
--
--   $$
--   v(\alpha,\gamma_i):=\Big[\frac{(\alpha^TX_i-\gamma_i)^2}{4\lambda_2}-\lambda_0\Big]_+ + M|\gamma_i|,\qquad
--   h_1(\alpha,\gamma):=-\tfrac12\|\alpha\|_2^2-\alpha^Ty-\sum_{i\in[p]}v(\alpha,\gamma_i).
--   $$
--
--   **The dual (22).** For $\rho\in\mathbb R^n$ and $\mu\in\mathbb R^p$, $h_2(\rho,\mu):=-\tfrac12\|\rho\|_2^2-\rho^Ty-M\|\mu\|_1$, and $(\rho,\mu)$ is feasible for (22) when $|\rho^TX_i|-\mu_i\le \lambda_0/M+\lambda_2M$ for every $i\in[p]$; $\mu$ is not sign-constrained.
--
--   **The dual variables (23)–(24).** For $\beta^*\in\mathbb R^p$ let $r^*=y-X\beta^*$, and
--
--   $$
--   \alpha^*=\rho^*=-r^*,\qquad
--   \gamma^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(\alpha^{*T}X_i-2M\lambda_2\,\mathrm{sign}(\alpha^{*T}X_i)\big),\qquad
--   \mu^*_i=\mathbb 1_{[|\beta^*_i|=M]}\big(|\rho^{*T}X_i|-\lambda_0/M-\lambda_2M\big).
--   $$
--
--   **The coordinate function of the proof.** For scalars $a$ (standing for $\alpha^TX_i$) and $\eta$ (a multiplier $\eta_i$), $D(b):=\psi_1(b;\lambda_0,\lambda_2)+ab+\eta|b|$, and $\tilde\beta$ is the point (45): $0$ if $2\sqrt{\lambda_0\lambda_2}+\eta-|a|\ge 0$ and $-\sqrt{\lambda_0/\lambda_2}\,\mathrm{sign}(a)$ otherwise.
--
--   These are the objects of Theorem 2, which states that (20) (when $\sqrt{\lambda_0/\lambda_2}\le M$) and (22) (when $\sqrt{\lambda_0/\lambda_2}>M$) are duals of (5) with optimal dual variables (23) and (24).
--
--   **Formalization Note** $\alpha^TX_i$ is `colDot X α i` $=\sum_r\alpha_rX_{ri}$; norms and inner products are explicit sums. sign is `Real.sign`, with $\mathrm{sign}(0)=0$. The dual variables are functions of an arbitrary $\beta^*$; that $\beta^*$ is optimal for (5) is a hypothesis of the theorems that use them.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, pp. 13–14, Theorem 2, (20)–(24); pp. 30–31, Proof of Theorem 2, (44)–(45)

import Mathlib
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Duality

/-! The Lagrangian duals (20)–(22) of the reduced relaxation (5), the dual variables (23)–(24)
(Theorem 2, pp. 13–14), and the one-coordinate function `Dᵢ` and the point (45) of the proof
of Theorem 2 (pp. 30–31) of Hazimeh, Mazumder, Saab, arXiv:2004.06152v2.

Conventions: `αᵀXᵢ = ∑ r, α r * X r i` (`Xᵢ` is the `i`-th column of `X`), `‖α‖₂² = ∑ r, α r ^ 2`,
`αᵀy = ∑ r, α r * y r`, `‖μ‖₁ = ∑ i, |μ i|`, `[a]₊ = max a 0`, and `sign = Real.sign`
(`Real.sign 0 = 0`). -/

/-- `αᵀXᵢ`, the inner product of `α ∈ ℝⁿ` with the `i`-th column of `X`. -/
def colDot {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (α : Fin n → ℝ) (i : Fin p) : ℝ :=
  ∑ r, α r * X r i

/-- (21), p. 13: `v(α, γᵢ) := [(αᵀXᵢ − γᵢ)²/(4λ₂) − λ₀]₊ + M|γᵢ|`. -/
noncomputable def v {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam0 lam2 M : ℝ)
    (α : Fin n → ℝ) (i : Fin p) (g : ℝ) : ℝ :=
  max ((colDot X α i - g) ^ 2 / (4 * lam2) - lam0) 0 + M * |g|

/-- The dual objective of (20), p. 13:
`h₁(α, γ) := −½‖α‖₂² − αᵀy − ∑_{i ∈ [p]} v(α, γᵢ)`. -/
noncomputable def h1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (α : Fin n → ℝ) (γ : Fin p → ℝ) : ℝ :=
  -(1 / 2) * ∑ r, α r ^ 2 - ∑ r, α r * y r - ∑ i, v X lam0 lam2 M α i (γ i)

/-- The dual objective of (22), p. 13: `h₂(ρ, μ) := −½‖ρ‖₂² − ρᵀy − M‖μ‖₁`. -/
noncomputable def h2 {n p : ℕ} (y : Fin n → ℝ) (M : ℝ) (ρ : Fin n → ℝ) (μ : Fin p → ℝ) : ℝ :=
  -(1 / 2) * ∑ r, ρ r ^ 2 - ∑ r, ρ r * y r - M * ∑ i, |μ i|

/-- The constraint of (22), p. 13: `|ρᵀXᵢ| − μᵢ ≤ λ₀/M + λ₂M` for every `i ∈ [p]`
(`μ` is not sign-constrained). -/
def Feas22 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam0 lam2 M : ℝ)
    (ρ : Fin n → ℝ) (μ : Fin p → ℝ) : Prop :=
  ∀ i, |colDot X ρ i| - μ i ≤ lam0 / M + lam2 * M

/-- The residual `r* = y − Xβ*` (Theorem 2, p. 14), as a function of `β*`. -/
def rStar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (βs : Fin p → ℝ) :
    Fin n → ℝ :=
  fun r => y r - Matrix.mulVec X βs r

/-- (23), p. 14: `α* = −r*`. -/
def alphaStar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (βs : Fin p → ℝ) :
    Fin n → ℝ :=
  fun r => -rStar X y βs r

/-- (23), p. 14: `γ*ᵢ = 𝟙[|β*ᵢ| = M] (α*ᵀXᵢ − 2Mλ₂ sign(α*ᵀXᵢ))`. -/
noncomputable def gammaStar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam2 M : ℝ) (βs : Fin p → ℝ) (i : Fin p) : ℝ :=
  if |βs i| = M then
    colDot X (alphaStar X y βs) i - 2 * M * lam2 * Real.sign (colDot X (alphaStar X y βs) i)
  else 0

/-- (24), p. 14: `ρ* = −r*`. -/
def rhoStar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (βs : Fin p → ℝ) :
    Fin n → ℝ :=
  fun r => -rStar X y βs r

/-- (24), p. 14: `μ*ᵢ = 𝟙[|β*ᵢ| = M] (|ρ*ᵀXᵢ| − λ₀/M − λ₂M)`. -/
noncomputable def muStar {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βs : Fin p → ℝ) (i : Fin p) : ℝ :=
  if |βs i| = M then |colDot X (rhoStar X y βs) i| - lam0 / M - lam2 * M else 0

/-- `Dᵢ(βᵢ) := ψ₁(βᵢ; λ₀, λ₂) + αᵀXᵢ βᵢ + ηᵢ|βᵢ|` (proof of Theorem 2, p. 30), written for a
scalar `a = αᵀXᵢ` and a scalar multiplier `η = ηᵢ`. -/
noncomputable def D (lam0 lam2 a η b : ℝ) : ℝ :=
  L0BnB.Reduced.psi1 lam0 lam2 b + a * b + η * |b|

/-- The point (45), p. 31: `0` if `2√(λ₀λ₂) + η − |a| ≥ 0`, and `−√(λ₀/λ₂) sign(a)` otherwise
(with `a = αᵀXᵢ`, `η = ηᵢ`). -/
noncomputable def betaTilde45 (lam0 lam2 a η : ℝ) : ℝ :=
  if 2 * Real.sqrt (lam0 * lam2) + η - |a| ≥ 0 then 0
  else -Real.sqrt (lam0 / lam2) * Real.sign a

end L0BnB.Duality


