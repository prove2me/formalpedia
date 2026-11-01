-- Prove2me | Definitions.Def_StochCoordProx_hessRows
-- name    : StochCoordProx_hessRows
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:23.486006+00:00
-- url     : https://prove2.me/theorems/f87f08a6-8292-4462-b66e-ab868a341590
-- title:
--   The matrix $\bar\nabla^2\Psi(z_1,\dots,z_n)$ (17)
-- statement:
--   For $\psi:\mathbb R^n\to\mathbb R$ and points $z_1,\dots,z_n\in\mathbb R^n$, let
--
--   $$
--   \bar\nabla^2\Psi(z_1,\dots,z_n)=\begin{bmatrix}\nabla_1^2\psi(z_1)\\ \vdots\\ \nabla_n^2\psi(z_n)\end{bmatrix}\in\mathbb R^{n\times n},
--   $$
--
--   where $\nabla_i^2\psi(z_i)$ is the $i$-th row of the Hessian of $\psi$ at $z_i$. Its entry $(i,j)$ is $\partial_j\partial_i\psi(z_i)$. Each row is evaluated at its own point, as in a coordinatewise mean value theorem.
--
--   **Formalization Note** The entry $(i,j)$ is the derivative at $z_i$ of the $i$-th coordinate of $\nabla\psi$ in the direction of the $j$-th standard basis vector.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, display (17), p.9

import Mathlib

namespace StochCoordProx

/-- **The matrix `∇̄²Ψ(z₁, …, zₙ)`** (display (17)): the `n × n` matrix whose `i`-th row is the
`i`-th row of the Hessian of `ψ` at the point `zᵢ ∈ ℝⁿ`. Its entry `(i, j)` is
`∂_j ∂_i ψ (zᵢ)`: the derivative, at `zᵢ`, of the `i`-th coordinate of `∇ψ` in the direction of
the `j`-th standard basis vector.

Necoara & Chorobura, arXiv:2104.13370v3, display (17), p.9.

**Formalization Note.** Row `i` is evaluated at its own point `z i` (a different point per row,
as in (17)). The entry is `fderiv ℝ (fun w => gradient ψ w i) (z i) (EuclideanSpace.single j 1)`;
for twice differentiable `ψ` this is the Hessian entry `(∇²ψ(zᵢ))_{ij}`. -/
noncomputable def hessRows {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (z : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun w => gradient ψ w i) (z i) (EuclideanSpace.single j 1)

end StochCoordProx


