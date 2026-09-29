-- Prove2me | Definitions.Def_SupportVectorMachines_Kernels_PositiveDefinite
-- name    : SupportVectorMachines_Kernels_PositiveDefinite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:58:11.633447+00:00
-- url     : https://prove2.me/theorems/d06e9ace-467e-4278-9f5c-ee9cf3f0d6d4
-- title:
--   Symmetric, positive definite, and strictly positive definite functions
-- statement:
--   Let $X$ be a non-empty set and $k : X \times X \to \mathbb R$ (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 4.15, p. 117).
--
--   $k$ is **symmetric** if $k(x,x') = k(x',x)$ for all $x,x' \in X$.
--
--   $k$ is **positive definite** if, for every $n \in \mathbb N$, every
--   $\alpha_1,\dots,\alpha_n \in \mathbb R$ and every $x_1,\dots,x_n \in X$,
--
--   $$
--   \sum_{i=1}^n \sum_{j=1}^n \alpha_i \alpha_j\, k(x_j, x_i) \ge 0.
--   $$
--
--   (Equivalently, the Gram matrix $K := (k(x_j,x_i))_{i,j}$ is positive semidefinite in the
--   usual matrix sense — the book notes some authors reserve the term "positive definite" for the
--   strict version below and call this weaker property "positive semi-definite".)
--
--   $k$ is **strictly positive definite** if, for every $n$ and every *mutually distinct*
--   $x_1,\dots,x_n \in X$, equality above forces $\alpha_1 = \cdots = \alpha_n = 0$.
--
--   Every kernel is automatically symmetric and positive definite (a two-line computation from
--   the feature-map definition); Theorem 4.16 is the converse.
--
--   **Formalization Note** The finite family $x_1,\dots,x_n$ (and $\alpha_1,\dots,\alpha_n$) is
--   represented as a function `Fin n → X` (resp. `Fin n → ℝ`) for an arbitrary `n : ℕ`, ranging
--   over every finite arity exactly as the book's "for all $n \in \mathbb N$" does.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 117, Definition 4.15

import Mathlib

namespace SupportVectorMachines.Kernels

/-- `k : X × X → ℝ` is **symmetric** (Definition 4.15, p. 117): `k(x,x') = k(x',x)` for all
`x, x' ∈ X`. -/
def Symmetric {X : Type*} (k : X → X → ℝ) : Prop := ∀ x x' : X, k x x' = k x' x

/-- `k : X × X → ℝ` is **positive definite** (Definition 4.15, p. 117, Eq. (4.5)): for every
finite collection `x₁,…,xₙ ∈ X` and `α₁,…,αₙ ∈ ℝ`, `∑ᵢ ∑ⱼ αᵢαⱼ k(xⱼ,xᵢ) ≥ 0`. The finite
collection is represented by a function `x : Fin n → X` (equivalently, `α : Fin n → ℝ`) for an
arbitrary `n : ℕ`, exactly as the book's "for all `n ∈ ℕ`, `α₁,…,αₙ`, `x₁,…,xₙ`" ranges over
every finite arity. -/
def PositiveDefinite {X : Type*} (k : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℝ) (x : Fin n → X), 0 ≤ ∑ i, ∑ j, α i * α j * k (x j) (x i)

/-- `k : X × X → ℝ` is **strictly positive definite** (Definition 4.15, p. 117): for every
`n : ℕ` and *mutually distinct* `x₁,…,xₙ ∈ X`, equality in (4.5) forces `α₁ = ⋯ = αₙ = 0`. -/
def StrictlyPositiveDefinite {X : Type*} (k : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℝ) (x : Fin n → X), Function.Injective x →
    (∑ i, ∑ j, α i * α j * k (x j) (x i) = 0) → ∀ i, α i = 0

end SupportVectorMachines.Kernels


