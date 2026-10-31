-- Prove2me | Definitions.Def_DissolveCDF_transJac
-- name    : DissolveCDF_transJac
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:51.679414+00:00
-- url     : https://prove2.me/theorems/a0e9a69a-bb05-4547-b5b9-a03deaabfb19
-- title:
--   §1.1, §2.1 — the transposed Jacobian $J_F(x)$
-- statement:
--   For a differentiable map $F:\mathbb R^n\to\mathbb R^m$ and $x\in\mathbb R^n$, the **transposed Jacobian** of $F$ at $x$ is the $n\times m$ matrix
--
--   $$
--   J_F(x)=\Big[\tfrac{\partial F_j(x)}{\partial x_i}\Big]_{i\le n,\ j\le m}=DF(x)^\top ,
--   $$
--
--   whose $j$-th column is the gradient $\nabla F_j(x)$. The paper writes $J_c(x)\in\mathbb R^{n\times p}$ for the constraint map and $J_{\mathcal A}(x)\in\mathbb R^{n\times n}$ for the constraint dissolving operator.
--
--   All gradient formulas of the mission are written with these matrices, e.g. $\nabla h(x)=J_{\mathcal A}(x)\nabla f(\mathcal A(x))+\beta J_c(x)c(x)$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, and $J_F(x)$ is the linear map $\mathbb R^m\to\mathbb R^n$ given by the Hilbert adjoint of the Fréchet derivative of $F$ at $x$; its operator norm is the paper's $\ell_2$ operator norm.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §1.1, p.1 (J_c) and §2.1, p.5 (J_A, the matrix display)

import Mathlib

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §1.1 (p.1) and §2.1 (p.5): the **transposed Jacobian** of a map
`F : ℝⁿ → ℝᵐ` at `x`, `J_F(x) = DF(x)ᵀ ∈ ℝ^{n×m}`, whose `i`-th column is `∇Fᵢ(x)`. The paper writes
`J_c(x)` for the constraint map `c` and `J_A(x)` for the constraint dissolving operator `A`.

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. The matrix `J_F(x)` is the linear map
`ℝᵐ → ℝⁿ` given by the Hilbert adjoint of the Fréchet derivative `fderiv ℝ F x : ℝⁿ → ℝᵐ`, so
`J_F(x)ᵀ` is `ContinuousLinearMap.adjoint (transJac F x) = fderiv ℝ F x`. The operator norm of
this linear map is the ℓ₂ operator norm of the paper (§2.1, p.5). -/
noncomputable def transJac {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (fderiv ℝ F x)

end DissolveCDF


