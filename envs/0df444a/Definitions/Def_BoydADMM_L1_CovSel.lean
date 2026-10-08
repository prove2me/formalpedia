-- Prove2me | Definitions.Def_BoydADMM_L1_CovSel
-- name    : BoydADMM_L1_CovSel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:02.22537+00:00
-- url     : https://prove2.me/theorems/d75d5991-462a-462b-90b2-782ddb830e45
-- title:
--   Sparse inverse covariance selection: the ADMM X- and Z-objectives and the eigenvalue X-update (§6.5)
-- statement:
--   Fix $n$, a symmetric matrix $S\in\mathbb R^{n\times n}$ (the empirical covariance), a penalty $\rho>0$ and a regularization weight $\lambda$. For real $n\times n$ matrices write
--   $$\|M\|_F^2=\sum_{i,j}M_{ij}^2,\qquad \|M\|_1=\sum_{i,j}|M_{ij}| .$$
--   The ADMM algorithm for sparse inverse covariance selection (§6.5, p. 46) alternates the two minimizations
--   $$X^{k+1}=\operatorname*{argmin}_{X\succ 0}\Bigl(\operatorname{Tr}(SX)-\log\det X+\tfrac{\rho}{2}\|X-Z^k+U^k\|_F^2\Bigr),\qquad Z^{k+1}=\operatorname*{argmin}_Z\Bigl(\lambda\|Z\|_1+\tfrac{\rho}{2}\|X^{k+1}-Z+U^k\|_F^2\Bigr),$$
--   followed by $U^{k+1}=U^k+X^{k+1}-Z^{k+1}$. This definition records the two objectives as functions of $X$ and of $Z$.
--
--   It also records the book's candidate X-update (p. 47). Given an orthogonal $Q$ and reals $\mu_1,\dots,\mu_n$ (the eigenvalues $\lambda_i$ of $\rho(Z^k-U^k)-S=Q\,\mathrm{diag}(\mu)\,Q^T$), put
--   $$r_\rho(\mu)=\frac{\mu+\sqrt{\mu^2+4\rho}}{2\rho},\qquad X=Q\,\mathrm{diag}\bigl(r_\rho(\mu_1),\dots,r_\rho(\mu_n)\bigr)\,Q^T .$$
--
--   These are the objects of the chapter's capstone: the X-update has an analytic solution through one eigenvalue decomposition.
--
--   **Formalization Note** The Frobenius norm and the elementwise $\ell_1$ norm are written out entrywise; Mathlib's default matrix norm is not used. The X-objective is a real function on all matrices, with $\log\det X$ computed by `Real.log`, but it is only ever minimized over positive definite $X$ (the domain of $\log\det$, p. 46), so its values at other matrices play no role. The book's regularization weight $\lambda$ is called `lam`, and its eigenvalues $\lambda_i$ are called $\mu_i$, because `λ` is a Lean keyword and the book uses the letter twice.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 46–47, §6.5 (ADMM algorithm for sparse inverse covariance selection; X̃_ii formula)

import Mathlib

open Matrix

namespace BoydADMM.L1

/-! Objects of §6.5 (sparse inverse covariance selection) of Boyd–Parikh–Chu–Peleato–Eckstein
(2011), pp. 45–47. Matrices are `Matrix (Fin n) (Fin n) ℝ`. The Frobenius norm and the
elementwise ℓ1 norm are written out entrywise; Mathlib's default matrix norm is not used. -/

/-- The squared Frobenius norm `‖M‖_F² = ∑_{i,j} M_{ij}²` (p. 47). -/
def frobSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j ^ 2

/-- The elementwise ℓ1 norm `‖M‖₁ = ∑_{i,j} |M_{ij}|` (p. 46). -/
def entrywiseL1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, |M i j|

/-- The X-minimization objective of the ADMM algorithm for sparse inverse covariance selection
(p. 46): `Tr(SX) − log det X + (ρ/2)‖X − Z + U‖_F²`. It is only ever minimized over positive
definite `X`, the domain of `log det`. -/
noncomputable def covselXObjective {n : ℕ} (S Z U : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (S * X) - Real.log X.det + (ρ / 2) * frobSq (X - Z + U)

/-- The Z-minimization objective (p. 46): `λ‖Z‖₁ + (ρ/2)‖X − Z + U‖_F²`; the regularization
weight `λ` is called `lam` (`λ` is a Lean keyword). -/
noncomputable def covselZObjective {n : ℕ} (lam ρ : ℝ) (X U : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  lam * entrywiseL1 Z + (ρ / 2) * frobSq (X - Z + U)

/-- The quadratic-formula root `(μ + √(μ² + 4ρ)) / (2ρ)` of `ρ t − 1/t = μ` (p. 47); `μ` stands
for the book's eigenvalue `λ_i`. -/
noncomputable def covselRoot (ρ μ : ℝ) : ℝ :=
  (μ + Real.sqrt (μ ^ 2 + 4 * ρ)) / (2 * ρ)

/-- The book's candidate X-update `X = Q X̃ Qᵀ` (p. 47), where
`X̃ = diag((μ_i + √(μ_i² + 4ρ)) / (2ρ))` and `μ_i` are the eigenvalues `λ_i` of
`ρ(Z − U) − S = Q diag(μ) Qᵀ`. -/
noncomputable def covselX {n : ℕ} (ρ : ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Q * Matrix.diagonal (fun i => covselRoot ρ (μ i)) * Qᵀ

end BoydADMM.L1


