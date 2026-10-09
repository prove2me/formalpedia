-- Prove2me | Definitions.Def_LasserreFC_Generic_Setting
-- name    : LasserreFC_Generic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:29.211009+00:00
-- url     : https://prove2.me/theorems/9e545e0a-1949-4dfe-9e57-08b2fb26b4ed
-- title:
--   (1.1)–(1.7), pp. 1–3, 14 — the polynomial optimization problem, its optimality conditions, H(u) and the space of input data
-- statement:
--   This file fixes the polynomial optimization problem (1.1) of Nie's paper, the classical optimality conditions at a point, the bordered Hessian $H(u)$ of §4.2, and the space of input data used in Theorem 1.2.
--
--   **The problem.** For polynomials $f, h_1,\dots,h_{m_1}, g_1,\dots,g_{m_2} \in \mathbb R[x]$, $x=(x_1,\dots,x_n)$, problem (1.1) is
--   $$\min\ f(x)\quad\text{s.t.}\quad h_i(x)=0\ (i\in[m_1]),\qquad g_j(x)\ge 0\ (j\in[m_2]),$$
--   with feasible set $K$; $m_1=0$ or $m_2=0$ is allowed. For $u\in K$, $J(u)=\{j : g_j(u)=0\}$ is the set of active inequality constraints. Gradients $\nabla p(u)$ and Hessians $\nabla^2 p(u)$ are those of the polynomial $p$.
--
--   **Optimality conditions (pp. 2–3).**
--   1. The *constraint qualification condition* (CQC) holds at $u$ if the vectors $\nabla h_1(u),\dots,\nabla h_{m_1}(u)$, $\nabla g_j(u)$ ($j\in J(u)$) are linearly independent.
--   2. $\lambda\in\mathbb R^{m_1}$, $\mu\in\mathbb R^{m_2}$ are *Lagrange multipliers* at $u$ if (1.3) $\nabla f(u)=\sum_i\lambda_i\nabla h_i(u)+\sum_j\mu_j\nabla g_j(u)$ and (1.4) $\mu_jg_j(u)=0$, $\mu_j\ge 0$ for all $j$.
--   3. *Strict complementarity* (1.5): $\mu_j+g_j(u)>0$ for all $j$.
--   4. With the Lagrange function $L(x)=f(x)-\sum_i\lambda_ih_i(x)-\sum_{j\in J(u)}\mu_jg_j(x)$, the *second order sufficiency condition* (1.7) is $v^T\nabla^2L(u)v>0$ for every $v\neq 0$ orthogonal to $\nabla h_i(u)$ for all $i$ and to $\nabla g_j(u)$ for all $j\in J(u)$.
--
--   "The constraint qualification, strict complementarity and second order sufficiency conditions hold at $u$" means: CQC holds, and there are multipliers satisfying (1.3), (1.4), (1.5) and (1.7).
--
--   **The matrix $H(u)$ (p. 14).** $G(u)$ is the matrix with rows $\nabla h_1(u)^T,\dots,\nabla h_{m_1}(u)^T$ followed by $\nabla g_j(u)^T$, $j\in J(u)$, and
--   $$H(u)=\begin{bmatrix}\nabla^2_xL(u) & G(u)^T\\ G(u) & 0\end{bmatrix}.$$
--
--   **Input data.** For degrees $d_0$, $d_i$ ($i\in[m_1]$), $d'_j$ ($j\in[m_2]$), the data are *admissible* if $f\in\mathbb R[x]_{d_0}$, $h_i\in\mathbb R[x]_{d_i}$, $g_j\in\mathbb R[x]_{d'_j}$, where $\mathbb R[x]_d$ is the space of polynomials of degree at most $d$. A *polynomial in the coefficients* of the input is a real polynomial in one variable per pair (polynomial, monomial), evaluated at the coefficient vector of $(f,h,g)$.
--
--   These are the objects in which Theorem 1.2, Propositions 4.4–4.5 and Lemma 4.6 are stated.
--
--   **Formalization Note** Points are vectors $\mathbb R^n$; gradients and Hessians are computed with formal partial derivatives, which agree with the analytic ones for polynomials. CQC is linear independence of the indexed family (so a repeated gradient counts twice). The coefficient variables include monomials of every degree; on admissible data those above the degree bound evaluate to zero, so "a polynomial that does not vanish" is always asserted at some admissible input, never as a nonzero formal polynomial.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 1–3, (1.1), (1.3)–(1.5), (1.7), Theorem 1.2; p. 14, L(x), G(x), H(x)

import Mathlib

namespace LasserreFC.Generic

open MvPolynomial Matrix

/-- Problem (1.1), p. 1: minimize `f` subject to `hᵢ(x) = 0` (`i ∈ [m₁]`) and `gⱼ(x) ≥ 0`
(`j ∈ [m₂]`), with `f, hᵢ, gⱼ ∈ ℝ[x]`, `x = (x₁, …, xₙ)`. `m₁ = 0` or `m₂ = 0` is allowed. -/
structure POP (n m1 m2 : ℕ) where
  /-- the objective `f` -/
  f : MvPolynomial (Fin n) ℝ
  /-- the equality constraints `h₁, …, h_{m₁}` -/
  h : Fin m1 → MvPolynomial (Fin n) ℝ
  /-- the inequality constraints `g₁, …, g_{m₂}` -/
  g : Fin m2 → MvPolynomial (Fin n) ℝ

variable {n m1 m2 : ℕ}

/-- The feasible set `K` of (1.1). -/
def POP.K (P : POP n m1 m2) : Set (Fin n → ℝ) :=
  {x | (∀ i, eval x (P.h i) = 0) ∧ ∀ j, 0 ≤ eval x (P.g j)}

/-- The gradient `∇p(u)` of a real polynomial, through formal partial derivatives. -/
noncomputable def grad (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun k => eval u (pderiv k p)

/-- The Hessian `∇²p(u)` of a real polynomial, through formal partial derivatives. -/
noncomputable def hess (p : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k s => eval u (pderiv k (pderiv s p))

/-- The active set `J(u) = {j ∈ [m₂] : gⱼ(u) = 0}`, as a type. -/
abbrev Active (P : POP n m1 m2) (u : Fin n → ℝ) : Type :=
  {j : Fin m2 // eval u (P.g j) = 0}

/-- The constraint qualification condition (CQC), p. 2: the family
`∇h₁(u), …, ∇h_{m₁}(u), ∇g_j(u) (j ∈ J(u))` is linearly independent (as an indexed family). -/
def CQC (P : POP n m1 m2) (u : Fin n → ℝ) : Prop :=
  LinearIndependent ℝ (Sum.elim (fun i : Fin m1 => grad (P.h i) u)
    (fun j : {j : Fin m2 // eval u (P.g j) = 0} => grad (P.g j.1) u))

/-- (1.3)–(1.4), p. 2: `λ, μ` are Lagrange multipliers at `u`:
`∇f(u) = Σᵢ λᵢ ∇hᵢ(u) + Σⱼ μⱼ ∇gⱼ(u)`, `μⱼ gⱼ(u) = 0` and `μⱼ ≥ 0` for all `j`. -/
def IsKKTMult (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u ∧
    (∀ j, mu j * eval u (P.g j) = 0) ∧ ∀ j, 0 ≤ mu j

/-- Strict complementarity (1.5), p. 2: `μⱼ + gⱼ(u) > 0` for every `j ∈ [m₂]`. -/
def SCC (P : POP n m1 m2) (u : Fin n → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  ∀ j, 0 < mu j + eval u (P.g j)

/-- The Lagrange function of p. 3 (and p. 14):
`L(x) = f(x) − Σᵢ λᵢ hᵢ(x) − Σ_{j ∈ J(u)} μⱼ gⱼ(x)`. -/
noncomputable def lagr (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  P.f - ∑ i, C (lam i) * P.h i -
    ∑ j ∈ Finset.univ.filter (fun j => eval u (P.g j) = 0), C (mu j) * P.g j

/-- The second order sufficiency condition (1.7), p. 3: `vᵀ ∇²L(u) v > 0` for every
`v ≠ 0` in `G(u)^⊥`, i.e. orthogonal to `∇hᵢ(u)` for all `i` and to `∇gⱼ(u)` for active `j`. -/
def SOSC (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 → (∀ i, grad (P.h i) u ⬝ᵥ v = 0) →
    (∀ j, eval u (P.g j) = 0 → grad (P.g j) u ⬝ᵥ v = 0) →
    0 < v ⬝ᵥ (hess (lagr P u lam mu) u *ᵥ v)

/-- "The constraint qualification, strict complementarity and second order sufficiency conditions
hold at `u`": CQC, and multipliers satisfying (1.3), (1.4), (1.5) and (1.7). -/
def OptCond (P : POP n m1 m2) (u : Fin n → ℝ) : Prop :=
  CQC P u ∧ ∃ lam mu, IsKKTMult P u lam mu ∧ SCC P u mu ∧ SOSC P u lam mu

/-- `G(u)`, p. 14: the matrix whose rows are `∇h₁(u), …, ∇h_{m₁}(u)` followed by `∇gⱼ(u)`,
`j ∈ J(u)` (in the CQC order). -/
noncomputable def Gmat (P : POP n m1 m2) (u : Fin n → ℝ) :
    Matrix (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}) (Fin n) ℝ :=
  Matrix.of (Sum.elim (fun i : Fin m1 => grad (P.h i) u)
    (fun j : {j : Fin m2 // eval u (P.g j) = 0} => grad (P.g j.1) u))

/-- `H(u) = [∇²ₓL(u), G(u)ᵀ; G(u), 0]`, p. 14. -/
noncomputable def Hmat (P : POP n m1 m2) (u : Fin n → ℝ) (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ) :
    Matrix (Fin n ⊕ (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0}))
      (Fin n ⊕ (Fin m1 ⊕ {j : Fin m2 // eval u (P.g j) = 0})) ℝ :=
  Matrix.fromBlocks (hess (lagr P u lam mu) u) (Gmat P u)ᵀ (Gmat P u) 0

/-- Admissible data for the degrees `d₀, dᵢ, d'ⱼ` (p. 3): `f ∈ ℝ[x]_{d₀}`, `hᵢ ∈ ℝ[x]_{dᵢ}`,
`gⱼ ∈ ℝ[x]_{d'ⱼ}`. -/
def POP.Admissible (P : POP n m1 m2) (d0 : ℕ) (d : Fin m1 → ℕ) (d' : Fin m2 → ℕ) : Prop :=
  P.f.totalDegree ≤ d0 ∧ (∀ i, (P.h i).totalDegree ≤ d i) ∧ ∀ j, (P.g j).totalDegree ≤ d' j

/-- One coefficient variable per (polynomial, monomial): `inl α` is the coefficient of `x^α` in
`f`, `inr (inl (i, α))` that in `hᵢ`, `inr (inr (j, α))` that in `gⱼ`. -/
abbrev CoefIdx (n m1 m2 : ℕ) : Type :=
  (Fin n →₀ ℕ) ⊕ ((Fin m1 × (Fin n →₀ ℕ)) ⊕ (Fin m2 × (Fin n →₀ ℕ)))

/-- The coefficient vector of the input data `(f, h, g)`. -/
noncomputable def coeffs (P : POP n m1 m2) : CoefIdx n m1 m2 → ℝ
  | Sum.inl α => P.f.coeff α
  | Sum.inr (Sum.inl (i, α)) => (P.h i).coeff α
  | Sum.inr (Sum.inr (j, α)) => (P.g j).coeff α

end LasserreFC.Generic


