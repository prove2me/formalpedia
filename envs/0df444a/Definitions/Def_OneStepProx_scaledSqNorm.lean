-- Prove2me | Definitions.Def_OneStepProx_scaledSqNorm
-- name    : OneStepProx_scaledSqNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:51.141687+00:00
-- url     : https://prove2.me/theorems/9719871c-4c24-4605-9e83-7ea2ca6d9513
-- title:
--   The squared scaled norm $\|x\|_C^2=\langle x,Cx\rangle$
-- statement:
--   For a real $d\times d$ matrix $C$ and a vector $x\in\mathbb R^d$, the **squared scaled norm** of $x$ is
--
--   $$
--   \|x\|_C^2=\langle x,Cx\rangle .
--   $$
--
--   For positive definite $C$ this is the square of the norm induced by $C$. It is the metric in which the scaled proximal operator of this mission is defined.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and a matrix acts on it through `Matrix.toEuclideanLin`.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, §1.2, p.5, "‖x‖²_C = ⟨x, Cx⟩ for every x in ℝd"

import Mathlib

open scoped RealInnerProductSpace

namespace OneStepProx

/-- The squared scaled norm `‖x‖²_C = ⟨x, Cx⟩` induced by a `d × d` real matrix `C`
(Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, §1.2, p.5).

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` and a matrix acts on it through
`Matrix.toEuclideanLin`. The paper uses this quantity for positive definite `C`; the definition
itself takes any matrix. -/
noncomputable def scaledSqNorm {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪x, Matrix.toEuclideanLin C x⟫

end OneStepProx


