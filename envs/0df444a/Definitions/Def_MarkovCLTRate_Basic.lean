-- Prove2me | Definitions.Def_MarkovCLTRate_Basic
-- name    : MarkovCLTRate_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:46.056714+00:00
-- url     : https://prove2.me/theorems/c51fed3f-c287-4e5c-888c-2fa1f6390b4a
-- title:
--   Euclidean space $\Re^d$, operator norm, matrix square roots, Hessian, Laplacian and the Wasserstein distance $d_{\mathcal W}$
-- statement:
--   This module fixes the finite-dimensional objects used throughout the paper.
--
--   Vectors live in $\Re^d$ with the standard Euclidean norm $\|\cdot\|$, and matrices are real $d\times d$ matrices. For a matrix $A$, the operator norm is
--   $$
--   \|A\|_{op}=\sup_{\|x\|=1}\|Ax\|.
--   $$
--   For a positive semidefinite matrix $A$, $A^{1/2}$ is its positive semidefinite square root and $A^{-1/2}=(A^{1/2})^{-1}$. For a twice differentiable $f:\Re^d\to\Re$, $\nabla^2 f(x)$ is the Hessian matrix and $\Delta f(x)=\sum_{i=1}^d\partial_{ii}f(x)$ the Laplacian.
--
--   The **Wasserstein distance** between two $d$-dimensional random vectors $X$ and $Y$ is
--   $$
--   d_{\mathcal W}(X,Y)=\sup_{h\in Lip_1}E[h(X)-h(Y)],\qquad Lip_L=\{h:\ |h(x)-h(y)|\le L\|x-y\|\}.
--   $$
--   It depends only on the laws of $X$ and $Y$, and it is the distance in which every rate of the paper is stated.
--
--   **Formalization Note** $\Re^d$ is `EuclideanSpace ℝ (Fin d)`, so `LipschitzWith 1` is the class $Lip_1$ for the Euclidean norm. The square root is Mathlib's `CFC.sqrt`, the one used to build `multivariateGaussian`. $d_{\mathcal W}$ takes values in $[0,\infty]$, so the supremum over the unbounded class $Lip_1$ is a genuine supremum; it is set to $\infty$ unless both measures are finite with a finite first moment, the case in which every $E[h(X)]$, $h\in Lip_1$, is defined.
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, §2.1, p.4 (d_W, Lip_L, ‖·‖_op); p.6 (V^{1/2}, V^{-1/2}); (2), p.5 (Δ, ∇²)

import Mathlib

open MeasureTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- `ℜ^d` with the standard Euclidean norm, Srikant, arXiv:2401.15719v5, §2.1, p.4.

**Formalization Note.** `EuclideanSpace ℝ (Fin d)` carries the Euclidean norm; `Fin d → ℝ` would
carry the sup norm and change the class `Lip_1`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real `d × d` matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The operator norm `‖A‖_op = sup_{‖x‖ = 1} ‖Ax‖` of a matrix, arXiv:2401.15719v5, p.4, computed
for the Euclidean norm on both sides. -/
noncomputable def opNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- The matrix acting on a vector of `ℜ^d`: `A x`. -/
noncomputable def mApply {d : ℕ} (A : Mat d) (x : Vec d) : Vec d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A x

/-- The matrix square root `A^{1/2}`, arXiv:2401.15719v5, p.6.

**Formalization Note.** This is Mathlib's `CFC.sqrt`, the same square root that defines
`multivariateGaussian`. It is only used on positive semidefinite matrices. -/
noncomputable def msqrt {d : ℕ} (A : Mat d) : Mat d := CFC.sqrt A

/-- The inverse square root `A^{-1/2} = (A^{1/2})^{-1}`, arXiv:2401.15719v5, p.6. Only used on
positive definite matrices (the matrix inverse is `0` on singular matrices). -/
noncomputable def minvSqrt {d : ℕ} (A : Mat d) : Mat d := (CFC.sqrt A)⁻¹

/-- The Hessian matrix `∇²f(x)`, entry `(i, j)` equal to `∂²f/∂x_i∂x_j(x)`, read off the second
Fréchet derivative in the standard basis. -/
noncomputable def hessMat {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Mat d :=
  Matrix.of fun i j =>
    fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- The Laplacian `Δf(x) = Σ_i ∂²f/∂x_i²(x)`, arXiv:2401.15719v5, (2), p.5. -/
noncomputable def laplacian {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

/-- The Wasserstein distance between the laws `μ`, `ν` of two `d`-dimensional random vectors,
arXiv:2401.15719v5, §2.1, p.4:
`d_W(X, Y) = sup_{h ∈ Lip_1} E[h(X) − h(Y)]`, where `Lip_1` is the class of functions
`h : ℜ^d → ℜ` with `|h(x) − h(y)| ≤ ‖x − y‖`.

**Formalization Note.** The value lies in `[0, ∞]` (`ℝ≥0∞`): a real supremum over the unbounded
family `Lip_1` would be Lean's junk value `0`. Every `h ∈ Lip_1` is integrable against a finite
measure with a finite first moment; for any other pair of measures the expectations in the
definition are not all defined, and the distance is set to `∞`. Since `−h ∈ Lip_1` whenever
`h ∈ Lip_1`, the supremum of the differences is nonnegative, so `ENNReal.ofReal` loses nothing. -/
noncomputable def dW {d : ℕ} (μ ν : Measure (Vec d)) : ℝ≥0∞ :=
  if μ Set.univ < ∞ ∧ ν Set.univ < ∞ ∧ (∫⁻ x, ‖x‖ₑ ∂μ) < ∞ ∧ (∫⁻ x, ‖x‖ₑ ∂ν) < ∞ then
    ⨆ (h : Vec d → ℝ) (_ : LipschitzWith 1 h), ENNReal.ofReal (∫ x, h x ∂μ - ∫ x, h x ∂ν)
  else ⊤

end MarkovCLTRate


