-- Prove2me | Definitions.Def_HighDimStat_Rkhs_Core
-- name    : HighDimStat_Rkhs_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:23:12.460954+00:00
-- url     : https://prove2.me/theorems/42e5a12b-a61d-4da9-ae8c-1563afa3e417
-- title:
--   PSD kernels, bounded evaluation functionals and the RKHS reproducing property
-- statement:
--   This file collects Chapter 12's core vocabulary for reproducing kernel Hilbert spaces
--   (RKHSs). `X` is an arbitrary index set (no topology needed for the Moore-Aronszajn
--   correspondence itself).
--
--   - **`IsPSDKernel K`**: a bivariate function $K:X\times X\to\mathbb R$ is a **positive
--     semidefinite (PSD) kernel** (Definition 12.6) if it is symmetric and, for every finite
--     collection of points $x_1,\dots,x_n\in X$ and weights $\alpha\in\mathbb R^n$,
--     $\sum_{i,j}\alpha_i\alpha_jK(x_i,x_j)\ge 0$ — equivalently, every Gram matrix
--     $(K(x_i,x_j))_{i,j}$ is positive semidefinite.
--   - **`HasBoundedEvalFunctionals toFun`**: for a Hilbert space $H$ presented via an
--     injective linear embedding `toFun` into functions on $X$, every evaluation functional
--     $f\mapsto f(x)$ is bounded (Definition 12.12): for each $x\in X$, there is $M<\infty$
--     with $|f(x)|\le M\|f\|_H$ for all $f\in H$.
--   - **`IsRKHS K toFun feature`**: $H$ (via `toFun`) is a reproducing kernel Hilbert space for
--     $K$, with feature map `feature` picking out $K(\cdot,x)\in H$ for each $x$ (Eq. (12.3)):
--     `toFun` is injective, $\mathrm{toFun}(\mathrm{feature}(x)) = K(\cdot,x)$ as a function,
--     and $\langle f,\mathrm{feature}(x)\rangle_H = f(x)$ for every $f\in H$, $x\in X$.
--
--   **Formalization Note** $H$ is presented throughout as an abstract Hilbert space together
--   with an injective linear map `toFun : H →ₗ[ℝ] (X → ℝ)` into the pointwise function space,
--   rather than as a literal subtype of `X → ℝ`; this keeps `H`'s own Hilbert-space structure
--   (`NormedAddCommGroup`, `InnerProductSpace ℝ`) as ordinary Mathlib instances while still
--   capturing "$H$ is a space of functions on $X$" via injectivity of `toFun`. `feature x` is
--   the element of $H$ the book calls $K(\cdot,x)$; `toFun (feature x)` recovers it as an
--   actual function $X\to\mathbb R$, checked equal to `fun z => K z x` (i.e. $z\mapsto K(z,x)$).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, pp. 386, 388, 390 (PDF pp. 406, 408, 410), Definitions 12.6, 12.12, Eq. (12.3)

import Mathlib

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- A positive semidefinite (PSD) kernel function (Definition 12.6, p. 386): a symmetric
bivariate function `K : X × X → ℝ` such that for every finite collection of points and
weights, the associated quadratic form is nonnegative -- equivalently, the `n × n` Gram
matrix `K(xᵢ, xⱼ)` is positive semidefinite for every `n` and every choice of points. -/
def IsPSDKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
    ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j)

/-- A Hilbert space `H`, presented via an injective linear embedding `toFun` into the space
of real-valued functions on `X`, has bounded evaluation functionals (Definition 12.12,
p. 390) if, for every point `x ∈ X`, the evaluation functional `f ↦ (toFun f) x` is a
bounded linear functional on `H`. -/
def HasBoundedEvalFunctionals {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) : Prop :=
  ∀ x : X, ∃ M : ℝ, ∀ f : H, |toFun f x| ≤ M * ‖f‖

/-- `H` (with embedding `toFun : H →ₗ[ℝ] (X → ℝ)` into functions on `X`) is a reproducing
kernel Hilbert space for the kernel `K`, with feature map `feature : X → H` picking out the
element `K(·, x) ∈ H` for every `x` (Eq. (12.3), p. 388): `toFun` is injective (so `H`
genuinely is a space of functions), `toFun (feature x)` really is the function `K(·, x)`,
and the reproducing property `⟨f, K(·,x)⟩_H = f(x)` holds for every `f ∈ H`, `x ∈ X`. -/
structure IsRKHS {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) : Prop where
  toFun_injective : Function.Injective toFun
  feature_eq : ∀ x : X, toFun (feature x) = fun z => K z x
  reproducing : ∀ (f : H) (x : X), ⟪f, feature x⟫ = toFun f x

end HighDimStat.Rkhs


