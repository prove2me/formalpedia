-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
-- name    : ConjGrad_ErrorDecrease_rayleigh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:54:10.732449+00:00
-- url     : https://prove2.me/theorems/58357995-de7e-4992-b5fe-52b2c88a1f7c
-- title:
--   The Rayleigh quotient $\mu(z)=(z,Az)/|z|^2$, eq. (4:12)
-- statement:
--   Let $A$ be a real $n\times n$ matrix. The **Rayleigh quotient** of a vector $z\in\mathbb{R}^n$ is
--
--   $$
--   \mu(z) = \frac{(z,Az)}{|z|^2}.
--   $$
--
--   For a symmetric positive definite $A$ and $z\neq 0$ it lies between the least and the largest eigenvalue of $A$, and in particular $\mu(z)>0$. In the error analysis of the cg-method it converts squared lengths of steps into decreases of the error function.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`. Lean's convention $t/0=0$ gives $\mu(0)=0$; the theorems of the mission only divide by $\mu(p_i)$ in situations where either $p_i\neq 0$ or the numerator is $0$ as well.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 413, eq. (4:12)

import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The Rayleigh quotient (4:12) of a vector `z` with respect to the matrix `A`:
`μ(z) = (z, Az) / |z|²`. Lean's convention `t / 0 = 0` gives `μ(0) = 0`. -/
noncomputable def rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) : ℝ :=
  (z ⬝ᵥ (A *ᵥ z)) / (z ⬝ᵥ z)

end ConjGrad.ErrorDecrease


