-- Prove2me | Definitions.Def_HunterPDE_Friedrichs_SymmetricOperator
-- name    : HunterPDE_Friedrichs_SymmetricOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:07.021583+00:00
-- url     : https://prove2.me/theorems/5f4214f8-fe52-4102-8c6c-b2ba38233ba9
-- title:
--   The first-order operator L = Aⁱ∂ᵢ + C and its formal adjoint L* (Eq. (8.3))
-- statement:
--   Let $n, m \ge 0$. Points of $\mathbb{R}^n$ are $x = (x_1,\dots,x_n)$, and vectors $w \in \mathbb{R}^m$ carry the Euclidean norm $|w|$. For a matrix $A \in \mathbb{R}^{m\times m}$, $Aw$ is the matrix–vector product. For $u : \mathbb{R}^n \to \mathbb{R}^m$ differentiable, $\partial_i u$ is its partial derivative in the $i$-th coordinate direction; for a matrix-valued $A : \mathbb{R}^n \to \mathbb{R}^{m\times m}$, $\partial_i A$ is the entrywise partial derivative.
--
--   Given coefficient matrices $A^1,\dots,A^n, C : \mathbb{R}^n \to \mathbb{R}^{m\times m}$, the operator of (8.3) and its formal adjoint are (summation over $i$)
--   $$Lu = A^i \partial_i u + C u, \qquad L^* v = -A^i \partial_i v + C^T v - (\partial_i A^i)\, v .$$
--   Integration by parts shows $\int v^T L u \,dx = \int u^T L^* v\,dx$ plus a boundary term when the $A^i$ are symmetric; this is the pairing used in the weak formulation of Friedrichs systems.
--
--   **Formalization Note.** $\mathbb{R}^n$ and $\mathbb{R}^m$ are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`; coordinates are 0-based, so Lean's `A i` is the book's $A^{i+1}$. `mv A w` is $Aw$, `pd u i x` is $\partial_i u(x)$ (the Fréchet derivative applied to the $i$-th basis vector), `matPd A i x` is $\partial_i A(x)$, and `Lop A C u x`, `Ladj A C v x` are $(Lu)(x)$ and $(L^*v)(x)$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 223, Eq. (8.3)

import Mathlib

open Matrix

namespace HunterPDE.Friedrichs

/-- The action `w ↦ A w` of an `m × m` real matrix on a vector `w ∈ ℝᵐ`, where `ℝᵐ` is the
Euclidean space `EuclideanSpace ℝ (Fin m)` (so that `|w|` is the Euclidean norm). -/
noncomputable def mv {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin A w

/-- The partial derivative `∂ᵢu(x)` of a vector-valued function `u : ℝⁿ → ℝᵐ` in the `i`-th
coordinate direction, `i : Fin n` (0-based: Lean's `i` is the book's `i + 1`). -/
noncomputable def pd {n m : ℕ} (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

/-- The entrywise partial derivative `∂ᵢA(x)` of a matrix-valued function
`A : ℝⁿ → ℝ^{m×m}` in the `i`-th coordinate direction (0-based `i : Fin n`). -/
noncomputable def matPd {n m : ℕ} (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => fderiv ℝ (fun y => A y j k) x (EuclideanSpace.single i 1)

/-- The first-order operator of Hunter (8.3), `L = Aⁱ∂ᵢ + C` (summation over `i`):
`(Lu)(x) = ∑ᵢ Aⁱ(x) ∂ᵢu(x) + C(x) u(x)` for `u : ℝⁿ → ℝᵐ`, with coefficient matrices
`Aⁱ, C : ℝⁿ → ℝ^{m×m}` (`A i` is the book's `A^{i+1}`). -/
noncomputable def Lop {n m : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  (∑ i, mv (A i x) (pd u i x)) + mv (C x) (u x)

/-- The formal adjoint of Hunter (8.3), `L* = −Aⁱ∂ᵢ + Cᵀ − ∂ᵢAⁱ` (summation over `i`):
`(L*v)(x) = −∑ᵢ Aⁱ(x) ∂ᵢv(x) + C(x)ᵀ v(x) − (∑ᵢ ∂ᵢAⁱ(x)) v(x)`. -/
noncomputable def Ladj {n m : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  -(∑ i, mv (A i x) (pd v i x)) + mv (C x)ᵀ (v x) - mv (∑ i, matPd (A i) i x) (v x)

end HunterPDE.Friedrichs


