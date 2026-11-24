-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel
-- name    : ConjGrad_ErrorDecrease_Supplement_IsSpectralModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:52:54.225875+00:00
-- url     : https://prove2.me/theorems/a4590b53-6aa5-484f-94e2-57d7ca5f4a7a
-- title:
--   Mass distribution on $[0,l]$ related to $A$ and $r_0$ as in §14
-- statement:
--   Let $A$ be an $n\times n$ real matrix and $r_0\in\mathbb R^n$. A **mass distribution** on $[0,l]$ is a nonnegative nondecreasing function $m(\lambda)$ on $0\le\lambda\le l$; it defines the Stieltjes integrals $\int_0^l f(\lambda)\,dm(\lambda)$ of continuous $f$. It is **related to $A$ and $r_0$ as described in §14** when there are
--
--   1. nodes $\lambda_1<\lambda_2<\cdots<\lambda_n$ and positive weights $m_1,\dots,m_n$ forming the $n$-point Gauss quadrature rule of $m$,
--   $$\int_0^l R(\lambda)\,dm(\lambda)=m_1R(\lambda_1)+\cdots+m_nR(\lambda_n)\quad\text{whenever }\deg R\le 2n-1, \tag{14:4}$$
--   2. orthonormal vectors $e_1,\dots,e_n$ with $Ae_j=\lambda_je_j$, and
--   3. coefficients $\alpha_j$ with $r_0=\alpha_1e_1+\cdots+\alpha_ne_n$ (14:5) and $\alpha_j^2=m_j$ (14:6).
--
--   Through this relation a polynomial $R$ of degree at most $n-1$ corresponds to the vector $R(A)r_0$, the linear extension of $\lambda^k\leftrightarrow A^kr_0$ (14:8). This is the bridge between orthogonal polynomials and the cg-method used in §§14–18.
--
--   **Formalization Note** The mass distribution is represented by its Lebesgue–Stieltjes measure $\mu$: a finite Borel measure on $\mathbb R$ with $\mu(\mathbb R\setminus[0,l])=0$, so that $\int_0^l f\,dm=\int f\,d\mu$ for continuous $f$. The Gauss rule is the published predicate `RQCMoments.IsGaussRule` (strictly increasing nodes, exactness up to degree $2n-1$, integrability included). `polyVec A r₀ R` is the vector $R(A)r_0$. The paper's dichotomy (infinitely many points of increase in $(0,l)$, or exactly $n$ of them) is not built in: any mass distribution carrying such an $n$-point rule qualifies, which includes both of the paper's cases.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 428, §14, pp. 428–429, eqs. (14:4)–(14:8) (PDF p. 20)

import Mathlib
import Definitions.Def_RQCMoments_IsGaussRule

open Matrix MeasureTheory

namespace ConjGrad.ErrorDecrease.Supplement

/-- The correspondence (14:8) of §14 (p. 429): the polynomial `R(λ)` corresponds to the vector
`R(A)r₀`, extending `λᵏ ↦ Aᵏr₀` linearly. -/
noncomputable def polyVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : Fin n → ℝ)
    (R : Polynomial ℝ) : Fin n → ℝ :=
  Polynomial.aeval A R *ᵥ r₀

/-- "A mass distribution `m(λ)` on `[0, l]` related to the matrix `A` and the vector `r₀` as
described" in §14 (pp. 428–429): `μ` is the (finite, Lebesgue–Stieltjes) measure of the mass
distribution, carried by `[0, l]`; there are an `n`-node Gauss quadrature rule (14:4) for `μ`
with nodes `λ₁ < ⋯ < λₙ` and positive weights `m₁, …, mₙ`, orthonormal eigenvectors
`e₁, …, eₙ` of `A` with `Aeⱼ = λⱼeⱼ`, and `r₀ = α₁e₁ + ⋯ + αₙeₙ` (14:5) with `αⱼ² = mⱼ` (14:6). -/
structure IsSpectralModel {n : ℕ} (μ : Measure ℝ) (l : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r₀ : Fin n → ℝ) : Prop where
  /-- the total mass is finite -/
  finite : IsFiniteMeasure μ
  /-- the mass sits on `[0, l]` -/
  support : μ (Set.Icc 0 l)ᶜ = 0
  /-- the Gauss rule and the eigen-data of `A` and `r₀` -/
  data : ∃ (lam w α : Fin n → ℝ) (e : Fin n → Fin n → ℝ),
    RQCMoments.IsGaussRule μ n lam w ∧ (∀ j, 0 < w j) ∧
    (∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0) ∧ (∀ j, A *ᵥ e j = lam j • e j) ∧
    r₀ = ∑ j, α j • e j ∧ ∀ j, α j ^ 2 = w j

end ConjGrad.ErrorDecrease.Supplement


