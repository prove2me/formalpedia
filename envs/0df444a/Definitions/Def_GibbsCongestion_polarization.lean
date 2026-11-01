-- Prove2me | Definitions.Def_GibbsCongestion_polarization
-- name    : GibbsCongestion_polarization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:24.754866+00:00
-- url     : https://prove2.me/theorems/ac5be083-83ee-49b2-a7a9-321b87729d05
-- title:
--   Polarization operator $\Pi_\kappa$
-- statement:
--   For $\kappa\in\mathbb Z^n_{\ge0}$, let $R_\kappa[x_i]$ be the polynomials of degree at most $\kappa_i$ in each $x_i$ and $R^a_\kappa[x_{ij}]$ the multi-affine polynomials in variables $x_{ij}$, $1\le i\le n$, $1\le j\le\kappa_i$. The **polarization operator** $\Pi_\kappa:R_\kappa[x_i]\to R^a_\kappa[x_{ij}]$ is linear and replaces every monomial $x^\alpha$ by
--   $$\binom{\kappa}{\alpha}^{-1}\prod_{i=1}^n e_{\alpha_i}(x_{i1},\dots,x_{i\kappa_i}),\qquad \binom{\kappa}{\alpha}=\prod_i\binom{\kappa_i}{\alpha_i},$$
--   where $e_k$ is the elementary symmetric polynomial of degree $k$. It turns a polynomial into a multi-affine one whose support is the set of bases of a matroid when the original is SLC and homogeneous.
--
--   **Formalization Note** The new variables are indexed by pairs $(i,j)$ with $j<\kappa_i$. The operator is applied only to polynomials of degree at most $\kappa_i$ in each $x_i$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.3, p.10

import Mathlib

namespace GibbsCongestion

/-- The **polarization operator** `Π_κ : R_κ[x_i] → R^a_κ[x_ij]` of Brändén and Huh
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.3, p.10): it is linear and replaces every monomial `x^α` by
`(κ choose α)⁻¹ ∏_i e_{α_i}(x_{i1}, …, x_{iκ_i})`, where `e_k` is the elementary symmetric
polynomial of degree `k` and `(κ choose α) = ∏_i (κ_i choose α_i)`.

**Formalization Note** The new variables `x_{ij}`, `1 ≤ j ≤ κ_i`, are indexed by the sigma type
`Σ i, Fin (κ i)`. The operator is meant for polynomials of degree at most `κ_i` in each `x_i`;
statements using it assume this. -/
noncomputable def polarization {σ : Type*} [Fintype σ] (κ : σ → ℕ) (p : MvPolynomial σ ℝ) :
    MvPolynomial (Σ i, Fin (κ i)) ℝ :=
  ∑ α ∈ p.support, MvPolynomial.C (p.coeff α * (∏ i, ((κ i).choose (α i) : ℝ))⁻¹) *
    ∏ i, MvPolynomial.rename (Sigma.mk i) (MvPolynomial.esymm (Fin (κ i)) ℝ (α i))

end GibbsCongestion


