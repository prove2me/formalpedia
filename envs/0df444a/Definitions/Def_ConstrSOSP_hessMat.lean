-- Prove2me | Definitions.Def_ConstrSOSP_hessMat
-- name    : ConstrSOSP_hessMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:41.550667+00:00
-- url     : https://prove2.me/theorems/cddb15ea-fed0-46c2-bb94-3858bc26234f
-- title:
--   Hessian $\nabla^2F(z)$ as a matrix
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$, the Hessian at $z$ is the matrix with entries $\partial_i\partial_jF(z)$, computed by differentiating the partial derivatives. For $C^2$ functions it is the symmetric Hessian.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.2, p.18

import Mathlib

namespace ConstrSOSP

/-- **Hessian `∇²F(z)` as a matrix**: entry `(i, j)` is `∂ᵢ ∂ⱼ F (z)`, the derivative in direction
`eᵢ` of `w ↦ ∂F/∂wⱼ (w)` at `z` (arXiv:2604.02285, 2 Nov 2026, §4.2, p.18).

**Formalization Note** Mathlib's `fderiv` applied twice; for `C²` functions this is the
(symmetric) Hessian. -/
noncomputable def hessMat {d : ℕ} (F : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fderiv ℝ (fun w => fderiv ℝ F w (Pi.single j 1)) z (Pi.single i 1)

end ConstrSOSP


