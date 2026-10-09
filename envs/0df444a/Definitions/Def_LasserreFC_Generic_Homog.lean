-- Prove2me | Definitions.Def_LasserreFC_Generic_Homog
-- name    : LasserreFC_Generic_Homog
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:26.63278+00:00
-- url     : https://prove2.me/theorems/9e0dde7e-f836-49c4-983e-0bc17a2e6499
-- title:
--   §2.1, (4.2)–(4.10), pp. 4, 10–12 — homogenisation, the systems (4.4), (4.5), (4.10), and nonsingularity of the KKT system
-- statement:
--   This file fixes the polynomial systems of §4.1 of Nie's paper, whose solvability is governed by the polynomials $\mathscr R$ and $\mathscr D$.
--
--   **Homogenisation (§2.1, p. 4).** For $p\in\mathbb R[x]_D$, $\tilde p(\tilde x)=x_0^{D}\,p(x/x_0)$, $\tilde x=(x_0,x_1,\dots,x_n)$, is the homogenisation of $p$ at the nominal degree $D$, a form of degree $D$ with complex coefficients. $\nabla_x\tilde p$ and $\nabla_x^2\tilde p$ are the gradient and Hessian in $x=(x_1,\dots,x_n)$ only; $\nabla\tilde p$ is the gradient in all of $\tilde x$.
--
--   **The system (4.5) (p. 10).** Given $p_0\in\mathbb R[x]_{d_0},\dots,p_k\in\mathbb R[x]_{d_k}$ and $q\in\mathbb R[x]_{d_{k+1}}$, (4.5) asks for $0\neq\tilde x\in\mathbb C^{n+1}$ with
--   $$\operatorname{rank}\big[\nabla_x\tilde p_0(\tilde x)\ \nabla_x\tilde p_1(\tilde x)\ \cdots\ \nabla_x\tilde p_k(\tilde x)\big]\le k,\qquad \tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=\tilde q(\tilde x)=0.$$
--   Its affine version (4.4) asks for $x\in\mathbb C^n$ with $\operatorname{rank}[\nabla_xp_0(x)\ \cdots\ \nabla_xp_k(x)]\le k$ and $p_1(x)=\cdots=p_k(x)=q(x)=0$.
--
--   **The system (4.10) (p. 12).** With the $(2n)\times(2k+1)$ matrix
--   $$\widetilde P(\tilde x,y)=\begin{bmatrix}\nabla_x\tilde p_0&\cdots&\nabla_x\tilde p_k&0&\cdots&0\\ (\nabla_x^2\tilde p_0)y&\cdots&(\nabla_x^2\tilde p_k)y&\nabla_x\tilde p_1&\cdots&\nabla_x\tilde p_k\end{bmatrix},$$
--   (4.10) asks for $\tilde x\in\mathbb C^{n+1}$, $y\in\mathbb C^n$, $\tilde x\neq0$, $y\neq0$, with $\operatorname{rank}\widetilde P(\tilde x,y)\le 2k$, $\tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=0$ and $(\nabla_x\tilde p_1)^Ty=\cdots=(\nabla_x\tilde p_k)^Ty=0$.
--
--   **Nonsingularity of the KKT system (p. 11).** A critical pair of $\min p_0$ s.t. $p_1=\cdots=p_k=0$ is $(x,\lambda)$ solving (4.2): $\nabla_xp_0(x)-\sum_i\lambda_i\nabla_xp_i(x)=0$, $p_1(x)=\cdots=p_k(x)=0$. The system (4.2) is *nonsingular* if
--   $$H_p(x,\lambda)=\begin{bmatrix}\nabla_x^2L_p(x,\lambda)&\operatorname{Jac}(p_1,\dots,p_k)|_x^T\\ \operatorname{Jac}(p_1,\dots,p_k)|_x&0\end{bmatrix},\qquad L_p=p_0-\sum_i\lambda_ip_i,$$
--   is nonsingular at every critical pair.
--
--   Finally, a tuple $(p_c)_c$ has coefficient vector with entry $(c,\alpha)$ equal to the coefficient of $x^\alpha$ in $p_c$.
--
--   **Formalization Note** The homogenisation is taken at the nominal degree $D$ (the degree bound of the input space), not at the actual degree, because $\mathscr R$ and $\mathscr D$ are polynomials on $\mathbb R[x]_{d_0}\times\cdots$; for a polynomial of lower degree this adds a factor of $x_0$. The constraints are indexed by an arbitrary finite type of size $k$, and the column of $p_0$ is a separate index; ranks are of complex matrices. Critical pairs and nonsingularity are taken over $\mathbb C$, which covers the real critical pairs.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 4, §2.1 (homogenization); pp. 10–12, (4.2), (4.4), (4.5), H_p(x, λ), P̃(x̃, y), (4.10)

import Mathlib

namespace LasserreFC.Generic

open MvPolynomial Matrix

variable {n : ℕ}

/-- Homogenisation at the nominal degree `D` (§2.1, p. 4):
`p̃(x̃) = x₀^D p(x/x₀)` for `x̃ = (x₀, x₁, …, xₙ)`, with complex coefficients. Variable `0` is
`x₀` and variable `k.succ` is `x_{k+1}`. On `p ∈ ℝ[x]_D` every exponent `D − |α|` is exact. -/
noncomputable def homog (D : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℂ :=
  ∑ α ∈ p.support, C (Complex.ofReal (p.coeff α)) * X 0 ^ (D - Finsupp.degree α) * ∏ k : Fin n, X k.succ ^ α k

/-- `∇ₓp̃(x̃)`: the gradient of `p̃` in `x = (x₁, …, xₙ)` only, at `x̃ ∈ ℂ^{n+1}`. -/
noncomputable def hgradx (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (xt : Fin (n + 1) → ℂ) :
    Fin n → ℂ :=
  fun k => eval xt (pderiv k.succ (homog D p))

/-- `∇p̃(x̃)`: the gradient of the form `p̃` in all variables `x̃ = (x₀, …, xₙ)` (as in (2.1)). -/
noncomputable def hgrad (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (xt : Fin (n + 1) → ℂ) :
    Fin (n + 1) → ℂ :=
  fun k => eval xt (pderiv k (homog D p))

/-- `∇²ₓp̃(x̃)`: the Hessian of `p̃` in `x = (x₁, …, xₙ)` only. -/
noncomputable def hhessx (D : ℕ) (p : MvPolynomial (Fin n) ℝ) (xt : Fin (n + 1) → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun k s => eval xt (pderiv k.succ (pderiv s.succ (homog D p)))

/-- The gradient of a real polynomial at a complex point `x ∈ ℂⁿ`. -/
noncomputable def cgrad (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun k => aeval x (pderiv k p)

/-- The Hessian of a real polynomial at a complex point `x ∈ ℂⁿ`. -/
noncomputable def chess (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k s => aeval x (pderiv k (pderiv s p))

variable {ι : Type*} [Fintype ι]

/-- The matrix `[∇ₓp̃₀(x̃) ∇ₓp̃ᵢ(x̃) (i ∈ ι)]` (`n` rows; column `none` is `p₀`). -/
noncomputable def gradMat45 (D0 : ℕ) (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ)
    (p : ι → MvPolynomial (Fin n) ℝ) (xt : Fin (n + 1) → ℂ) : Matrix (Fin n) (Option ι) ℂ :=
  Matrix.of fun k c => Option.elim c (hgradx D0 p0 xt k) (fun i => hgradx (D i) (p i) xt k)

/-- The system (4.5), p. 10, for `p₀` and constraints `pᵢ` (`i ∈ ι`, `|ι| = k`) and `q`, with
nominal degrees `D0, D i, Dq`: there is `0 ≠ x̃ ∈ ℂ^{n+1}` with
`rank [∇ₓp̃₀(x̃) ∇ₓp̃₁(x̃) ⋯ ∇ₓp̃ₖ(x̃)] ≤ k` and `p̃₁(x̃) = ⋯ = p̃ₖ(x̃) = q̃(x̃) = 0`. -/
def Sys45 (D0 : ℕ) (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ) (p : ι → MvPolynomial (Fin n) ℝ)
    (Dq : ℕ) (q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
    (gradMat45 D0 p0 D p xt).rank ≤ Fintype.card ι ∧
    (∀ i, eval xt (homog (D i) (p i)) = 0) ∧ eval xt (homog Dq q) = 0

/-- The system (4.4), p. 10, over `ℂⁿ`: there is `x ∈ ℂⁿ` with
`rank [∇ₓp₀(x) ∇ₓp₁(x) ⋯ ∇ₓpₖ(x)] ≤ k` and `p₁(x) = ⋯ = pₖ(x) = q(x) = 0`. -/
def Sys44 (p0 : MvPolynomial (Fin n) ℝ) (p : ι → MvPolynomial (Fin n) ℝ)
    (q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ x : Fin n → ℂ,
    (Matrix.of fun (k : Fin n) (c : Option ι) =>
        Option.elim c (cgrad p0 x k) (fun i => cgrad (p i) x k)).rank ≤ Fintype.card ι ∧
    (∀ i, aeval x (p i) = 0) ∧ aeval x q = 0

/-- The `(2n) × (2k + 1)` matrix `P̃(x̃, y)` of p. 12:
`[∇ₓp̃₀ ⋯ ∇ₓp̃ₖ, 0 ⋯ 0; (∇²ₓp̃₀)y ⋯ (∇²ₓp̃ₖ)y, ∇ₓp̃₁ ⋯ ∇ₓp̃ₖ]`.
Rows: `inl k` top block, `inr k` bottom block; columns: `inl c` the first `k + 1`
(`none` is `p₀`), `inr i` the last `k`. -/
noncomputable def Ptilde (D0 : ℕ) (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ)
    (p : ι → MvPolynomial (Fin n) ℝ) (xt : Fin (n + 1) → ℂ) (y : Fin n → ℂ) :
    Matrix (Fin n ⊕ Fin n) (Option ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (gradMat45 D0 p0 D p xt) 0
    (Matrix.of fun k c => Option.elim c ((hhessx D0 p0 xt *ᵥ y) k)
      (fun i => (hhessx (D i) (p i) xt *ᵥ y) k))
    (Matrix.of fun k i => hgradx (D i) (p i) xt k)

/-- The system (4.10), p. 12: there are `x̃ ∈ ℂ^{n+1}`, `y ∈ ℂⁿ`, `x̃ ≠ 0`, `y ≠ 0`, with
`rank P̃(x̃, y) ≤ 2k`, `p̃₁(x̃) = ⋯ = p̃ₖ(x̃) = 0` and
`(∇ₓp̃₁)ᵀy = ⋯ = (∇ₓp̃ₖ)ᵀy = 0`. -/
def Sys410 (D0 : ℕ) (p0 : MvPolynomial (Fin n) ℝ) (D : ι → ℕ)
    (p : ι → MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧ ∃ y : Fin n → ℂ, y ≠ 0 ∧
    (Ptilde D0 p0 D p xt y).rank ≤ 2 * Fintype.card ι ∧
    (∀ i, eval xt (homog (D i) (p i)) = 0) ∧
    ∀ i, hgradx (D i) (p i) xt ⬝ᵥ y = 0

/-- A critical pair `(x, λ) ∈ ℂⁿ × ℂ^k` of (4.1), i.e. a solution of the KKT system (4.2), p. 10:
`∇ₓp₀(x) − Σᵢ λᵢ∇ₓpᵢ(x) = 0`, `p₁(x) = ⋯ = pₖ(x) = 0`. -/
def IsCriticalPair (p0 : MvPolynomial (Fin n) ℝ) (p : ι → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℂ) (lam : ι → ℂ) : Prop :=
  cgrad p0 x - ∑ i, lam i • cgrad (p i) x = 0 ∧ ∀ i, aeval x (p i) = 0

/-- `H_p(x, λ) = [∇²ₓL_p(x, λ), Jac(p₁, …, pₖ)|ₓᵀ; Jac(p₁, …, pₖ)|ₓ, 0]`, p. 11, with
`L_p(x, λ) = p₀(x) − Σᵢ λᵢ pᵢ(x)`. -/
noncomputable def Hp (p0 : MvPolynomial (Fin n) ℝ) (p : ι → MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℂ) (lam : ι → ℂ) : Matrix (Fin n ⊕ ι) (Fin n ⊕ ι) ℂ :=
  Matrix.fromBlocks (chess p0 x - ∑ i, lam i • chess (p i) x)
    (Matrix.of fun (i : ι) (k : Fin n) => cgrad (p i) x k)ᵀ
    (Matrix.of fun (i : ι) (k : Fin n) => cgrad (p i) x k) 0

/-- "(4.2) is a nonsingular system" (p. 11): `H_p(x, λ)` is nonsingular at every critical pair
`(x, λ)`, here every complex critical pair. -/
def KKTNonsingular [DecidableEq ι] (p0 : MvPolynomial (Fin n) ℝ)
    (p : ι → MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ (x : Fin n → ℂ) (lam : ι → ℂ), IsCriticalPair p0 p x lam → (Hp p0 p x lam).det ≠ 0

/-- The coefficient vector of a tuple `(P c)_{c ∈ τ}` of real polynomials: the variable `(c, α)`
is the coefficient of `x^α` in `P c`. -/
noncomputable def tupleCoeffs {τ : Type*} (P : τ → MvPolynomial (Fin n) ℝ) :
    τ × (Fin n →₀ ℕ) → ℝ :=
  fun c => (P c.1).coeff c.2

end LasserreFC.Generic


