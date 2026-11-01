-- Prove2me | Definitions.Def_StochCoordProx_model
-- name    : StochCoordProx_model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:26.345975+00:00
-- url     : https://prove2.me/theorems/c42b5bf1-58a5-4e52-ab89-9300f58d81f9
-- title:
--   SCPG subproblem objective (9)
-- statement:
--   At the current point $x\in\mathbb R^n$, with sampled matrix $U\in\mathbb R^{n\times p}$ and parameter $H=H_{f,U}$, SCPG minimizes over $d\in\mathbb R^p$ the function
--
--   $$
--   f(x)+\langle U^T\nabla f(x),d\rangle+\frac H2\|d\|^2+\psi(x+Ud).
--   $$
--
--   It combines a sketch $U^T\nabla f(x)$ of the gradient of $f$ with the exact restriction of $\psi$ to the subspace. Minimizing it is a proximal step of $\psi$ along the subspace, never the full proximal operator of $\psi$.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Algorithm 1 (SCPG), step 2, display (9), p.6

import Mathlib

open Matrix
open scoped InnerProductSpace

namespace StochCoordProx

/-- **The SCPG subproblem objective** (display (9)): at the current point `x ∈ ℝⁿ`, with sampled
matrix `U ∈ ℝ^{n×p}` and parameter `H = H_{f,U}`, the function of `d ∈ ℝᵖ`
`f(x) + ⟨Uᵀ∇f(x), d⟩ + (H/2)‖d‖² + ψ(x + U d)`.
Algorithm 1 takes `d_k ∈ argmin_{d ∈ ℝᵖ}` of this function.

Necoara & Chorobura, arXiv:2104.13370v3, Algorithm 1 (SCPG), step 2, display (9), p.6.

**Formalization Note.** Euclidean spaces `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin p)`;
`U` acts as `Matrix.toEuclideanLin U` and `Uᵀ` as `Matrix.toEuclideanLin Uᵀ`; `∇f` is
`gradient f`. -/
noncomputable def model {n p : ℕ} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (U : Matrix (Fin n) (Fin p) ℝ) (H : ℝ)
    (d : EuclideanSpace ℝ (Fin p)) : ℝ :=
  f x + ⟪Matrix.toEuclideanLin Uᵀ (gradient f x), d⟫_ℝ + H / 2 * ‖d‖ ^ 2 +
    ψ (x + Matrix.toEuclideanLin U d)

end StochCoordProx


