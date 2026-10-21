-- Prove2me | Definitions.Def_MatrixAnalytic_Spectral_Polynomial
-- name    : MatrixAnalytic_Spectral_Polynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:18.12941+00:00
-- url     : https://prove2.me/theorems/88f82769-b9fe-4123-ba15-3c17231644bc
-- title:
--   The matrix polynomials Γ(x), Ξ(x), Φ_G(x), Φ_R(x), Γ⁽¹⁾(x), the determinant γ(x), and towers
-- statement:
--   Let $A_0, A_1, A_2$ be real $m \times m$ matrices, read as complex matrices, and let $I$ be the identity.
--
--   1. The matrix polynomial (9.2) and its determinant:
--   $$\Gamma(x) = x^2 A_0 + x(A_1 - I) + A_2, \qquad \gamma(x) = \det \Gamma(x),$$
--   with $\gamma$ a polynomial with complex coefficients of degree at most $2m$; its roots are counted with multiplicity.
--   2. The derivative $\Gamma^{(1)}(x) = 2xA_0 + A_1 - I$.
--   3. For a complex matrix $G$, $\Phi_G(x) = xA_0 + A_1 - I + A_0G$.
--   4. $\Xi(x) = x^2A_2 + x(A_1 - I) + A_0$ and, for a complex matrix $R$, $\Phi_R(x) = xA_2 + A_1 - I + RA_2$.
--   5. **Towers** (p. 214). Given a matrix $G$, a scalar $\lambda$ and $p \ge 1$, the column vectors $v_p, v_{p-1}, \dots, v_1$ are **in a tower** for $G$ relative to $\lambda$ if $v_1$ is an eigenvector of $G$ for $\lambda$ (that is, $v_1 \ne 0$ and $(\lambda I - G)v_1 = 0$) and $v_i = (\lambda I - G)v_{i+1}$ for $1 \le i \le p-1$.
--
--   **Formalization Note** $\Gamma$ appears twice: as a matrix with entries in $\mathbb C[x]$ (`GammaPoly`, whose determinant is the polynomial `gammaPoly`) and evaluated at a point $x \in \mathbb C$ (`GammaAt`). The vectors of a tower are a function `v : ℕ → ι → ℂ` of which only the indices $1, \dots, p$ are used.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 212, Eq. (9.2) and Eq. (9.3); pp. 212–213 (Ξ, Φ_R); p. 214 (towers); p. 215, Theorem 9.4.2 (Γ⁽¹⁾)

import Mathlib

namespace MatrixAnalytic.Spectral

noncomputable section

open Polynomial Matrix

/-!
The polynomial matrices of §9.3–9.4 of Latouche & Ramaswami (pp. 212–215), built from the blocks
`A₀, A₁, A₂` of a QBD with finitely many phases (`m = card ι`) and, where the book's formula
involves them, from given matrices `G` and `R`. Real blocks are mapped to `ℂ`, since the roots of
`γ(x) = det Γ(x)` are complex. `Γ(x)` is given both as a matrix of polynomials (whose determinant is
the polynomial `γ`, with its roots counted with multiplicity by `Polynomial.roots`) and as the
complex matrix `Γ(x)` at a point `x ∈ ℂ`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real matrix (given entrywise) read as a complex matrix. -/
def cMat (A : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ((A i j : ℝ) : ℂ)

/-- The matrix polynomial (9.2), `Γ(x) = x²A₀ + x(A₁ − I) + A₂`, as a matrix with entries in `ℂ[X]`. -/
def GammaPoly (A₀ A₁ A₂ : ι → ι → ℝ) : Matrix ι ι ℂ[X] :=
  (X ^ 2 : ℂ[X]) • (cMat A₀).map C + (X : ℂ[X]) • (cMat A₁ - 1).map C + (cMat A₂).map C

/-- `γ(x) = det(Γ(x))` (p. 212), a polynomial with complex coefficients of degree at most `2m`. -/
def gammaPoly (A₀ A₁ A₂ : ι → ι → ℝ) : ℂ[X] :=
  (GammaPoly A₀ A₁ A₂).det

/-- `Γ(x) = x²A₀ + x(A₁ − I) + A₂` (9.2) evaluated at a point `x ∈ ℂ`. -/
def GammaAt (A₀ A₁ A₂ : ι → ι → ℝ) (x : ℂ) : Matrix ι ι ℂ :=
  x ^ 2 • cMat A₀ + x • (cMat A₁ - 1) + cMat A₂

/-- `Γ⁽¹⁾(x) = 2xA₀ + A₁ − I`, the derivative of `Γ` (Theorem 9.4.2, p. 215). -/
def Gamma1At (A₀ A₁ : ι → ι → ℝ) (x : ℂ) : Matrix ι ι ℂ :=
  (2 * x) • cMat A₀ + (cMat A₁ - 1)

/-- `Φ_G(x) = xA₀ + A₁ − I + A₀G` (p. 212), for a given complex matrix `G`. -/
def PhiG (A₀ A₁ : ι → ι → ℝ) (G : Matrix ι ι ℂ) (x : ℂ) : Matrix ι ι ℂ :=
  x • cMat A₀ + (cMat A₁ - 1) + cMat A₀ * G

/-- `Ξ(x) = x²A₂ + x(A₁ − I) + A₀` (p. 212), the matrix polynomial of the equation for `R`. -/
def XiAt (A₀ A₁ A₂ : ι → ι → ℝ) (x : ℂ) : Matrix ι ι ℂ :=
  x ^ 2 • cMat A₂ + x • (cMat A₁ - 1) + cMat A₀

/-- `Φ_R(x) = xA₂ + A₁ − I + RA₂` (p. 213), for a given complex matrix `R`. -/
def PhiR (A₁ A₂ : ι → ι → ℝ) (R : Matrix ι ι ℂ) (x : ℂ) : Matrix ι ι ℂ :=
  x • cMat A₂ + (cMat A₁ - 1) + R * cMat A₂

/-- Vectors "in a tower" (p. 214): the column vectors `v₁, …, v_p` (`v : ℕ → ι → ℂ`, indices
`1, …, p`) are in a tower for the matrix `G` relative to `λ` if `v₁` is an eigenvector of `G` for
`λ` (nonzero, `(λI − G)v₁ = 0`) and `vᵢ = (λI − G)vᵢ₊₁` for `1 ≤ i ≤ p − 1`. -/
def InTower (G : Matrix ι ι ℂ) (lam : ℂ) (p : ℕ) (v : ℕ → ι → ℂ) : Prop :=
  v 1 ≠ 0 ∧ (lam • (1 : Matrix ι ι ℂ) - G) *ᵥ v 1 = 0 ∧
    ∀ i : ℕ, 1 ≤ i → i + 1 ≤ p → v i = (lam • (1 : Matrix ι ι ℂ) - G) *ᵥ v (i + 1)

end

end MatrixAnalytic.Spectral


