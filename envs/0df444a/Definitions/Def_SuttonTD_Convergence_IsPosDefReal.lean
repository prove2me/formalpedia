-- Prove2me | Definitions.Def_SuttonTD_Convergence_IsPosDefReal
-- name    : SuttonTD_Convergence_IsPosDefReal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:28.427035+00:00
-- url     : https://prove2.me/theorems/f2e57eae-d722-4d3f-9e03-97519be1a82f
-- title:
--   Positive definite in the sense of footnote 6: $y^\top A y>0$ for all real $y\ne0$
-- statement:
--   Following footnote 6 of the paper, a real square matrix $A$ is **positive definite** if
--
--   $$y^{\top}A\,y>0\qquad\text{for every real vector } y\neq 0 .$$
--
--   The matrix need not be symmetric. This is the notion applied to the non-symmetric matrix $D(I-Q)$ in the convergence proof of linear TD(0).
--
--   **Formalization Note** This differs from Mathlib's `Matrix.PosDef`, which additionally requires the matrix to be Hermitian.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, footnote 6, p. 27 (PDF p. 19)

import Mathlib
open Matrix

namespace SuttonTD.Convergence

/-- Positive definiteness in the sense of Sutton 1988, footnote 6 (§4.1, p. 27, PDF p. 19):
"A matrix `A` is positive definite if and only if `yᵀAy > 0` for all real vectors `y ≠ 0`."

Formalization Note: this notion does **not** require `A` to be symmetric, unlike Mathlib's
`Matrix.PosDef` (which also asks for Hermitian). The paper applies it to the non-symmetric matrix
`D(I − Q)`. -/
def IsPosDefReal {n : Type*} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  ∀ y : n → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (A *ᵥ y)

end SuttonTD.Convergence


