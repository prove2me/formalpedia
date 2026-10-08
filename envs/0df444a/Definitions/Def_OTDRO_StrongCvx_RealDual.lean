-- Prove2me | Definitions.Def_OTDRO_StrongCvx_RealDual
-- name    : OTDRO_StrongCvx_RealDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:25.582796+00:00
-- url     : https://prove2.me/theorems/d43ca029-3d02-42d8-84f4-352609ee3315
-- title:
--   Real representative of the finite dual objective
-- statement:
--   The dual objective $f_\delta(\beta,\lambda)$ is extended-real-valued. On a neighborhood where it is finite, its real representative is
--
--   $$f_\delta^{\mathbb R}(\beta,\lambda)=f_\delta(\beta,\lambda)\in\mathbb R.$$
--
--   Theorems 3–4 differentiate this representative to state Hessian bounds. Their statements include neighborhood finiteness, so no conclusion relies on the default real value of an infinite extended-real number.
--
--   **Formalization Note** Lean implements the representative with `EReal.toReal`; it agrees with $f_\delta$ only where the latter is neither $+\infty$ nor $-\infty$.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Theorem 1, p. 10; Theorems 3–4, p. 11

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Regions

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Real representative of f_δ on a neighborhood where f_δ is finite.
The theorems using it explicitly require that neighborhood to be finite. -/
noncomputable def dualReal {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (θ : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  (OTDRO.Dual.fDelta P0 ℓ A δ θ.1 θ.2).toReal

end OTDRO.StrongCvx


